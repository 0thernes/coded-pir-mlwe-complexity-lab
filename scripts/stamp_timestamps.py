#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander S. Donahue
"""Dual cryptographic timestamping & verification for MANIFEST.sha256 (Playbook v1.3 Item 26):
1. RFC 3161 Trusted Timestamping Authority (`data/MANIFEST.sha256.tsr` via DigiCert TSA)
2. Bitcoin OpenTimestamps (`data/MANIFEST.sha256.ots` via 3 public OTS calendar servers)
"""

from __future__ import annotations

import argparse
import hashlib
import re
import shutil
import subprocess
import tempfile
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST_PATH = ROOT / "MANIFEST.sha256"
TSR_PATH = ROOT / "data" / "MANIFEST.sha256.tsr"
OTS_PATH = ROOT / "data" / "MANIFEST.sha256.ots"

TSA_URL = "http://timestamp.digicert.com"
OTS_CALENDARS = [
    "https://a.pool.opentimestamps.org/digest",
    "https://b.pool.opentimestamps.org/digest",
    "https://a.pool.eternitywall.com/digest",
]
OTS_MAGIC = b"\x00OpenTimestamps\x00\x00Proof\x00\xbf\x89\xe2\xe8\x84\xe8\x92\x94\x01"
OTS_SHA256_OP = b"\x08"
OTS_PENDING_TAG = bytes.fromhex("83dfe30d2ef90c8e")
OTS_BITCOIN_TAG = bytes.fromhex("0588960d73d71901")


def find_openssl() -> str:
    found = shutil.which("openssl")
    if found:
        return found
    for cand in (
        Path(r"C:\Program Files\Git\usr\bin\openssl.exe"),
        Path(r"C:\Program Files\Git\mingw64\bin\openssl.exe"),
    ):
        if cand.is_file():
            return str(cand)
    raise FileNotFoundError("openssl binary not found on PATH")


def sha256_bytes(path: Path) -> bytes:
    return hashlib.sha256(path.read_bytes()).digest()


def stamp_rfc3161(manifest: Path, out_tsr: Path) -> str:
    openssl = find_openssl()
    with tempfile.TemporaryDirectory() as td:
        tsq = Path(td) / "manifest.tsq"
        r = subprocess.run(
            [openssl, "ts", "-query", "-data", str(manifest), "-sha256", "-cert", "-no_nonce", "-out", str(tsq)],
            capture_output=True,
            text=True,
            check=False,
        )
        if r.returncode != 0:
            raise RuntimeError(f"openssl ts -query failed: {r.stderr}")
        req = urllib.request.Request(
            TSA_URL,
            data=tsq.read_bytes(),
            headers={"Content-Type": "application/timestamp-query"},
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=20.0) as resp:
            tsr_bytes = resp.read()
        out_tsr.write_bytes(tsr_bytes)
    return verify_rfc3161(manifest, out_tsr)


def stamp_ots(manifest: Path, out_ots: Path) -> int:
    digest = sha256_bytes(manifest)
    branches: list[bytes] = []
    for url in OTS_CALENDARS:
        req = urllib.request.Request(
            url,
            data=digest,
            headers={
                "Content-Type": "application/x-www-form-urlencoded",
                "Accept": "application/vnd.opentimestamps.v1",
                "User-Agent": "TriadFrontier-OTS/1.0",
            },
            method="POST",
        )
        try:
            with urllib.request.urlopen(req, timeout=15.0) as resp:
                body = resp.read()
                if body and (OTS_PENDING_TAG in body or OTS_BITCOIN_TAG in body):
                    branches.append(body)
        except (urllib.error.URLError, TimeoutError, OSError):
            continue
    if not branches:
        raise RuntimeError("Failed to obtain OpenTimestamps commitment from any public calendar")
    # Standard OTS v1 proof wire format: magic + hash_op(0x08) + 32-byte digest + forks (0xff) + final branch
    payload = bytearray(OTS_MAGIC)
    payload.extend(OTS_SHA256_OP)
    payload.extend(digest)
    for idx, br in enumerate(branches):
        if idx < len(branches) - 1:
            payload.append(0xFF)
        payload.extend(br)
    out_ots.write_bytes(bytes(payload))
    return len(branches)


def parse_tsr_message_digest(openssl_text: str) -> str:
    m = re.search(r"Message data:\s*\n((?:\s*[0-9a-fA-F]{4}\s*-\s*[0-9a-fA-F -]+.*\n)+)", openssl_text)
    if not m:
        raise ValueError("Could not parse Message data block from TSR")
    hex_bytes: list[str] = []
    for line in m.group(1).splitlines():
        parts = line.split("-", 1)
        if len(parts) != 2:
            continue
        hex_part = parts[1][:49].replace("-", " ")
        for tok in hex_part.split():
            if len(tok) == 2 and all(c in "0123456789abcdefABCDEF" for c in tok):
                hex_bytes.append(tok.lower())
    return "".join(hex_bytes)


def find_ca_bundle() -> str | None:
    """Locate a root CA certificate bundle for full cryptographic RFC 3161 TSA verification."""
    candidates = [
        Path("/etc/ssl/certs/ca-certificates.crt"),
        Path("/etc/pki/tls/certs/ca-bundle.crt"),
        Path("/etc/ssl/cert.pem"),
        Path(r"C:\Program Files\Git\usr\ssl\certs\ca-bundle.crt"),
        Path(r"C:\Program Files\Git\mingw64\etc\ssl\certs\ca-bundle.crt"),
    ]
    for cand in candidates:
        if cand.is_file():
            return str(cand)
    try:
        import certifi  # type: ignore[import-not-found]

        p = Path(certifi.where())
        if p.is_file():
            return str(p)
    except ImportError:
        pass
    return None


def verify_rfc3161(manifest: Path, tsr: Path) -> str:
    if not tsr.is_file():
        raise FileNotFoundError(f"Missing RFC 3161 receipt: {tsr}")
    openssl = find_openssl()
    ca_bundle = find_ca_bundle()
    if ca_bundle is None:
        raise FileNotFoundError("Root CA bundle not found for cryptographic openssl ts -verify")
    v = subprocess.run(
        [openssl, "ts", "-verify", "-data", str(manifest), "-in", str(tsr), "-CAfile", ca_bundle],
        capture_output=True,
        text=True,
        check=False,
    )
    if v.returncode != 0 or "Verification: OK" not in v.stdout:
        raise ValueError(f"Cryptographic RFC 3161 signature/chain verification failed: {v.stdout} {v.stderr}")
    r = subprocess.run(
        [openssl, "ts", "-reply", "-in", str(tsr), "-text"],
        capture_output=True,
        text=True,
        check=False,
    )
    if r.returncode != 0:
        raise RuntimeError(f"openssl ts -reply failed: {r.stderr}")
    text = r.stdout
    if "Status: Granted." not in text:
        raise ValueError("RFC 3161 TSR status is not Granted")
    expected_hex = sha256_bytes(manifest).hex()
    actual_hex = parse_tsr_message_digest(text)
    if actual_hex != expected_hex:
        raise ValueError(f"RFC 3161 TSR digest mismatch: got {actual_hex}, expected {expected_hex}")
    serial_m = re.search(r"Serial number:\s*(\S+)", text)
    time_m = re.search(r"Time stamp:\s*(.+)", text)
    serial = serial_m.group(1) if serial_m else "unknown"
    ts_str = time_m.group(1).strip() if time_m else "unknown"
    return f"RFC3161 CRYPTO-OK (serial={serial}, time={ts_str}, sha256={expected_hex[:16]}...)"


def verify_ots(manifest: Path, ots: Path) -> str:
    if not ots.is_file():
        raise FileNotFoundError(f"Missing OpenTimestamps receipt: {ots}")
    raw = ots.read_bytes()
    header = OTS_MAGIC + OTS_SHA256_OP
    if not raw.startswith(header) or len(raw) < len(header) + 32 + 10:
        raise ValueError("Invalid OpenTimestamps header or truncated proof")
    embedded = raw[len(header) : len(header) + 32]
    expected = sha256_bytes(manifest)
    if embedded != expected:
        raise ValueError(f"OpenTimestamps digest mismatch: got {embedded.hex()}, expected {expected.hex()}")
    rest = raw[len(header) + 32 :]
    pending_cnt = rest.count(OTS_PENDING_TAG)
    btc_cnt = rest.count(OTS_BITCOIN_TAG)
    if pending_cnt + btc_cnt < 1:
        raise ValueError("OpenTimestamps proof contains zero calendar or Bitcoin attestations")
    return (
        f"OTS OK (sha256={expected.hex()[:16]}..., "
        f"pending_calendars={pending_cnt}, bitcoin_attestations={btc_cnt}, bytes={len(raw)})"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description="Stamp or verify RFC 3161 + OpenTimestamps receipts.")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--stamp", action="store_true", help="Create fresh .tsr and .ots receipts for MANIFEST.sha256")
    group.add_argument("--verify", action="store_true", help="Verify existing .tsr and .ots receipts against MANIFEST.sha256")
    parser.add_argument("--manifest", type=Path, default=MANIFEST_PATH)
    parser.add_argument("--tsr", type=Path, default=TSR_PATH)
    parser.add_argument("--ots", type=Path, default=OTS_PATH)
    args = parser.parse_args()

    if args.stamp:
        tsr_info = stamp_rfc3161(args.manifest, args.tsr)
        cals = stamp_ots(args.manifest, args.ots)
        ots_info = verify_ots(args.manifest, args.ots)
        print(f"STAMPED ({cals} OTS calendars): {tsr_info} | {ots_info}")
        return 0

    tsr_info = verify_rfc3161(args.manifest, args.tsr)
    ots_info = verify_ots(args.manifest, args.ots)
    print(f"VERIFIED: {tsr_info} | {ots_info}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
