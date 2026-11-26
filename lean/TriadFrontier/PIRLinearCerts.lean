module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import TriadFrontier.PIRCertificates

/-!
# Exact F_2 / F_3 Linear-Subspace Certificates for `h_uncond` (`T1i`, `CS-053`)

Zero-Mathlib, zero-`native_decide`, O(log N) balanced-tree kernel certificates proving:
1. All 23 explicit F_2/F_3 linear-subspace 4-variable rays match `subspaceRank4` of their
   generator matrices inside the Lean kernel (`checkLinRay4Exact_ok`).
2. All 24 canonical 4-marginal profiles of `h_uncond` decompose at common denominator `3`
   as nonnegative integer combinations of those 23 linear rays (`checkCanonDecomp4_ok`).
3. ALL 495 singleton 4-marginals (`C(12,4)`) and ALL 15 retrieval-object 4-marginals (`C(6,4)`)
   of `h_uncond` match `canonProf4` under an explicit S_4 coordinate permutation (`checkAll510Marg4_ok`).
4. ALL `C(6,5) = 6` five-object retrieval marginals of `{W1, W2, A1, A2, A3, A4}` in `h_uncond`
   decompose as exact nonnegative integer combinations of explicit F_2-linear subspace arrangements
   (`Core_W1` in F_2^8, `G1` in F_2^8, `G2` in F_2^12, and 1-dim Boolean rays; `checkAll6RetMarg5_ok`).
-/

namespace TriadFrontier.PIRLinearCerts

open TriadFrontier.PIRCertificates

@[expose] public section

/-- Exact Gaussian elimination rank over F_p (for p = 2 or 3 where every nonzero element is self-inverse!). -/
def matRankModP (p : Nat) (rows : List (List Nat)) : Nat :=
  let rec go (col fuel : Nat) (A : List (List Nat)) (rk : Nat) : Nat :=
    match fuel with
    | 0 => rk
    | fuel' + 1 =>
      match A.find? (fun r => r.getD col 0 % p != 0) with
      | none => go (col + 1) fuel' A rk
      | some piv =>
        let pv := piv.getD col 0 % p
        let pivNorm := piv.map (fun x => (x * pv) % p)
        let rest := A.erase piv
        let elim := rest.map (fun r =>
          let f := r.getD col 0 % p
          if f == 0 then r
          else (r.zip pivNorm).map (fun (a, b) => (a + p * p - (f * b) % p) % p))
        go (col + 1) fuel' elim (rk + 1)
  match rows with
  | [] => 0
  | r0 :: _ => go 0 r0.length rows 0

/-- Exact subspace-arrangement rank profile on 4 subspaces over F_p (`mask ∈ 1..15`). -/
def subspaceRank4 (p : Nat) (subs : List (List (List Nat))) (mask : Nat) : Nat :=
  let s0 := if (mask &&& 1) != 0 then subs.getD 0 [] else []
  let s1 := if (mask &&& 2) != 0 then subs.getD 1 [] else []
  let s2 := if (mask &&& 4) != 0 then subs.getD 2 [] else []
  let s3 := if (mask &&& 8) != 0 then subs.getD 3 [] else []
  matRankModP p (s0 ++ s1 ++ s2 ++ s3)

/-- Exact subspace-arrangement rank profile on 5 subspaces over F_p (`mask ∈ 1..31`). -/
def subspaceRank5 (p : Nat) (subs : List (List (List Nat))) (mask : Nat) : Nat :=
  let s0 := if (mask &&& 1) != 0 then subs.getD 0 [] else []
  let s1 := if (mask &&& 2) != 0 then subs.getD 1 [] else []
  let s2 := if (mask &&& 4) != 0 then subs.getD 2 [] else []
  let s3 := if (mask &&& 8) != 0 then subs.getD 3 [] else []
  let s4 := if (mask &&& 16) != 0 then subs.getD 4 [] else []
  matRankModP p (s0 ++ s1 ++ s2 ++ s3 ++ s4)

/-- Recursive integer linear functional evaluator `∑_{j=1}^k c(j) * r(j)`. -/
def evalFuncGo (c : Nat → Int) (r : Nat → Nat) : Nat → Int
  | 0 => 0
  | k + 1 => evalFuncGo c r k + c (k + 1) * Int.ofNat (r (k + 1))

/-- Evaluate a 4-variable integer linear functional `c` (on masks 1..15) on a rank function `r`. -/
def evalFunc4 (c : Nat → Int) (r : Nat → Nat) : Int :=
  evalFuncGo c r 15

/-- Evaluate a 5-variable integer linear functional `c` (on masks 1..31) on a rank function `r`. -/
def evalFunc5 (c : Nat → Int) (r : Nat → Nat) : Int :=
  evalFuncGo c r 31

/-- The 23 explicit F_2 / F_3 linear-subspace 4-variable arrangements spanning every 4-marginal of `h_uncond`. -/
def linRay4Spec : List (Nat × List (List (List Nat))) := [

  (2, [[], [], [], [[1]]]), -- ray 0: B1 (F_2)
  (2, [[], [], [[1]], []]), -- ray 1: B1 (F_2)
  (2, [[], [], [[1]], [[1]]]), -- ray 2: B2 (F_2)
  (2, [[], [[1]], [], []]), -- ray 3: B1 (F_2)
  (2, [[], [[1]], [], [[1]]]), -- ray 4: B2 (F_2)
  (2, [[], [[1, 0]], [[0, 1]], [[1, 1]]]), -- ray 5: U23_0 (F_2)
  (2, [[[1]], [], [], []]), -- ray 6: B1 (F_2)
  (2, [[[1]], [], [], [[1]]]), -- ray 7: B2 (F_2)
  (2, [[[1]], [], [[1]], []]), -- ray 8: B2 (F_2)
  (2, [[[1, 0]], [], [[0, 1]], [[1, 1]]]), -- ray 9: U23_0 (F_2)
  (2, [[[1]], [[1]], [], []]), -- ray 10: B2 (F_2)
  (2, [[[1, 1]], [[1, 1]], [[1, 0]], [[0, 1]]]), -- ray 11: U23_dup (F_2)
  (2, [[[1, 0]], [[0, 1]], [], [[1, 1]]]), -- ray 12: U23_0 (F_2)
  (2, [[[1, 1]], [[1, 0]], [[1, 1]], [[0, 1]]]), -- ray 13: U23_dup (F_2)
  (2, [[[1, 0]], [[0, 1]], [[1, 1]], []]), -- ray 14: U23_0 (F_2)
  (3, [[[1, 0]], [[0, 1]], [[1, 1]], [[1, 2]]]), -- ray 15: U24 (F_3)
  (2, [[[1, 0, 0]], [[0, 1, 0]], [[0, 0, 1]], [[1, 1, 1]]]), -- ray 16: U34 (F_2)
  (2, [[[1, 0, 1]], [[0, 1, 1]], [[0, 0, 1]], [[1, 0, 0], [0, 1, 0]]]), -- ray 17: R3_4 (F_2)
  (2, [[[1, 0, 1]], [[0, 1, 1]], [[1, 0, 0], [0, 1, 0]], [[0, 0, 1]]]), -- ray 18: R3_4 (F_2)
  (2, [[[0, 1, 0]], [[1, 0, 0], [0, 0, 1]], [[0, 0, 1]], [[1, 0, 0], [0, 1, 0]]]), -- ray 19: R3_pair2 (F_2)
  (2, [[[0, 1, 0]], [[1, 0, 0], [0, 0, 1]], [[1, 0, 0], [0, 1, 0]], [[0, 0, 1]]]), -- ray 20: R3_pair2 (F_2)
  (2, [[[1, 0, 0], [0, 1, 0]], [[0, 0, 1]], [[0, 1, 0]], [[1, 0, 0], [0, 0, 1]]]), -- ray 21: R3_pair2 (F_2)
  (2, [[[1, 0, 0], [0, 1, 0]], [[0, 0, 1]], [[1, 0, 0], [0, 0, 1]], [[0, 1, 0]]]) -- ray 22: R3_pair2 (F_2)
]

def linRay4At (r k : Nat) : Nat :=
  let idx := r * 15 + k
  (if idx < 173 then (if idx < 87 then (if idx < 44 then (if idx < 22 then (if idx < 11 then (if idx < 6 then (if idx < 3 then (if idx < 2 then (if idx < 1 then 0 else 0) else 0) else (if idx < 5 then (if idx < 4 then 0 else 0) else 0)) else (if idx < 9 then (if idx < 8 then (if idx < 7 then 0 else 1) else 1) else (if idx < 10 then 1 else 1))) else (if idx < 17 then (if idx < 14 then (if idx < 13 then (if idx < 12 then 1 else 1) else 1) else (if idx < 16 then (if idx < 15 then 1 else 0) else 0)) else (if idx < 20 then (if idx < 19 then (if idx < 18 then 0 else 1) else 1) else (if idx < 21 then 1 else 1)))) else (if idx < 33 then (if idx < 28 then (if idx < 25 then (if idx < 24 then (if idx < 23 then 0 else 0) else 0) else (if idx < 27 then (if idx < 26 then 0 else 1) else 1)) else (if idx < 31 then (if idx < 30 then (if idx < 29 then 1 else 1) else 0) else (if idx < 32 then 0 else 0))) else (if idx < 39 then (if idx < 36 then (if idx < 35 then (if idx < 34 then 1 else 1) else 1) else (if idx < 38 then (if idx < 37 then 1 else 1) else 1)) else (if idx < 42 then (if idx < 41 then (if idx < 40 then 1 else 1) else 1) else (if idx < 43 then 1 else 1))))) else (if idx < 66 then (if idx < 55 then (if idx < 50 then (if idx < 47 then (if idx < 46 then (if idx < 45 then 1 else 0) else 1) else (if idx < 49 then (if idx < 48 then 1 else 0) else 0)) else (if idx < 53 then (if idx < 52 then (if idx < 51 then 1 else 1) else 0) else (if idx < 54 then 0 else 1))) else (if idx < 61 then (if idx < 58 then (if idx < 57 then (if idx < 56 then 1 else 0) else 0) else (if idx < 60 then (if idx < 59 then 1 else 1) else 0)) else (if idx < 64 then (if idx < 63 then (if idx < 62 then 1 else 1) else 0) else (if idx < 65 then 0 else 1)))) else (if idx < 77 then (if idx < 72 then (if idx < 69 then (if idx < 68 then (if idx < 67 then 1 else 1) else 1) else (if idx < 71 then (if idx < 70 then 1 else 1) else 1)) else (if idx < 75 then (if idx < 74 then (if idx < 73 then 1 else 1) else 1) else (if idx < 76 then 0 else 1))) else (if idx < 82 then (if idx < 80 then (if idx < 79 then (if idx < 78 then 1 else 1) else 1) else (if idx < 81 then 2 else 2)) else (if idx < 85 then (if idx < 84 then (if idx < 83 then 1 else 1) else 2) else (if idx < 86 then 2 else 2)))))) else (if idx < 130 then (if idx < 109 then (if idx < 98 then (if idx < 93 then (if idx < 90 then (if idx < 89 then (if idx < 88 then 2 else 2) else 2) else (if idx < 92 then (if idx < 91 then 1 else 0) else 1)) else (if idx < 96 then (if idx < 95 then (if idx < 94 then 0 else 1) else 0) else (if idx < 97 then 1 else 0))) else (if idx < 104 then (if idx < 101 then (if idx < 100 then (if idx < 99 then 1 else 0) else 1) else (if idx < 103 then (if idx < 102 then 0 else 1) else 0)) else (if idx < 107 then (if idx < 106 then (if idx < 105 then 1 else 1) else 0) else (if idx < 108 then 1 else 0)))) else (if idx < 120 then (if idx < 115 then (if idx < 112 then (if idx < 111 then (if idx < 110 then 1 else 0) else 1) else (if idx < 114 then (if idx < 113 then 1 else 1) else 1)) else (if idx < 118 then (if idx < 117 then (if idx < 116 then 1 else 1) else 1) else (if idx < 119 then 1 else 1))) else (if idx < 125 then (if idx < 123 then (if idx < 122 then (if idx < 121 then 1 else 0) else 1) else (if idx < 124 then 1 else 1)) else (if idx < 128 then (if idx < 127 then (if idx < 126 then 1 else 1) else 0) else (if idx < 129 then 1 else 0))))) else (if idx < 152 then (if idx < 141 then (if idx < 136 then (if idx < 133 then (if idx < 132 then (if idx < 131 then 1 else 1) else 1) else (if idx < 135 then (if idx < 134 then 1 else 1) else 1)) else (if idx < 139 then (if idx < 138 then (if idx < 137 then 0 else 1) else 1) else (if idx < 140 then 2 else 1))) else (if idx < 147 then (if idx < 144 then (if idx < 143 then (if idx < 142 then 2 else 1) else 2) else (if idx < 146 then (if idx < 145 then 1 else 2) else 2)) else (if idx < 150 then (if idx < 149 then (if idx < 148 then 2 else 2) else 2) else (if idx < 151 then 1 else 1)))) else (if idx < 163 then (if idx < 158 then (if idx < 155 then (if idx < 154 then (if idx < 153 then 1 else 0) else 1) else (if idx < 157 then (if idx < 156 then 1 else 1) else 0)) else (if idx < 161 then (if idx < 160 then (if idx < 159 then 1 else 1) else 1) else (if idx < 162 then 0 else 1))) else (if idx < 168 then (if idx < 166 then (if idx < 165 then (if idx < 164 then 1 else 1) else 1) else (if idx < 167 then 1 else 1)) else (if idx < 171 then (if idx < 170 then (if idx < 169 then 1 else 2) else 2) else (if idx < 172 then 2 else 1))))))) else (if idx < 259 then (if idx < 216 then (if idx < 195 then (if idx < 184 then (if idx < 179 then (if idx < 176 then (if idx < 175 then (if idx < 174 then 2 else 2) else 2) else (if idx < 178 then (if idx < 177 then 2 else 2) else 2)) else (if idx < 182 then (if idx < 181 then (if idx < 180 then 2 else 1) else 1) else (if idx < 183 then 2 else 0))) else (if idx < 190 then (if idx < 187 then (if idx < 186 then (if idx < 185 then 1 else 1) else 2) else (if idx < 189 then (if idx < 188 then 1 else 2) else 2)) else (if idx < 193 then (if idx < 192 then (if idx < 191 then 2 else 1) else 2) else (if idx < 194 then 2 else 2)))) else (if idx < 206 then (if idx < 201 then (if idx < 198 then (if idx < 197 then (if idx < 196 then 1 else 1) else 2) else (if idx < 200 then (if idx < 199 then 1 else 1) else 2)) else (if idx < 204 then (if idx < 203 then (if idx < 202 then 2 else 1) else 2) else (if idx < 205 then 2 else 2))) else (if idx < 211 then (if idx < 209 then (if idx < 208 then (if idx < 207 then 2 else 2) else 2) else (if idx < 210 then 2 else 1)) else (if idx < 214 then (if idx < 213 then (if idx < 212 then 1 else 2) else 1) else (if idx < 215 then 2 else 2))))) else (if idx < 238 then (if idx < 227 then (if idx < 222 then (if idx < 219 then (if idx < 218 then (if idx < 217 then 2 else 0) else 1) else (if idx < 221 then (if idx < 220 then 1 else 2) else 1)) else (if idx < 225 then (if idx < 224 then (if idx < 223 then 2 else 2) else 2) else (if idx < 226 then 1 else 1))) else (if idx < 233 then (if idx < 230 then (if idx < 229 then (if idx < 228 then 2 else 1) else 2) else (if idx < 232 then (if idx < 231 then 2 else 2) else 1)) else (if idx < 236 then (if idx < 235 then (if idx < 234 then 2 else 2) else 2) else (if idx < 237 then 2 else 2)))) else (if idx < 249 then (if idx < 244 then (if idx < 241 then (if idx < 240 then (if idx < 239 then 2 else 2) else 1) else (if idx < 243 then (if idx < 242 then 1 else 2) else 1)) else (if idx < 247 then (if idx < 246 then (if idx < 245 then 2 else 2) else 3) else (if idx < 248 then 1 else 2))) else (if idx < 254 then (if idx < 252 then (if idx < 251 then (if idx < 250 then 2 else 3) else 2) else (if idx < 253 then 3 else 3)) else (if idx < 257 then (if idx < 256 then (if idx < 255 then 3 else 1) else 1) else (if idx < 258 then 2 else 1)))))) else (if idx < 302 then (if idx < 281 then (if idx < 270 then (if idx < 265 then (if idx < 262 then (if idx < 261 then (if idx < 260 then 2 else 2) else 3) else (if idx < 264 then (if idx < 263 then 2 else 3) else 3)) else (if idx < 268 then (if idx < 267 then (if idx < 266 then 3 else 3) else 3) else (if idx < 269 then 3 else 3))) else (if idx < 276 then (if idx < 273 then (if idx < 272 then (if idx < 271 then 1 else 1) else 2) else (if idx < 275 then (if idx < 274 then 2 else 3) else 3)) else (if idx < 279 then (if idx < 278 then (if idx < 277 then 3 else 1) else 2) else (if idx < 280 then 2 else 3)))) else (if idx < 292 then (if idx < 287 then (if idx < 284 then (if idx < 283 then (if idx < 282 then 3 else 3) else 3) else (if idx < 286 then (if idx < 285 then 3 else 1) else 2)) else (if idx < 290 then (if idx < 289 then (if idx < 288 then 3 else 1) else 2) else (if idx < 291 then 2 else 3))) else (if idx < 297 then (if idx < 295 then (if idx < 294 then (if idx < 293 then 2 else 2) else 3) else (if idx < 296 then 3 else 3)) else (if idx < 300 then (if idx < 299 then (if idx < 298 then 3 else 3) else 3) else (if idx < 301 then 1 else 2))))) else (if idx < 324 then (if idx < 313 then (if idx < 308 then (if idx < 305 then (if idx < 304 then (if idx < 303 then 3 else 2) else 2) else (if idx < 307 then (if idx < 306 then 3 else 3) else 1)) else (if idx < 311 then (if idx < 310 then (if idx < 309 then 2 else 2) else 3) else (if idx < 312 then 3 else 3))) else (if idx < 319 then (if idx < 316 then (if idx < 315 then (if idx < 314 then 3 else 3) else 2) else (if idx < 318 then (if idx < 317 then 1 else 3) else 1)) else (if idx < 322 then (if idx < 321 then (if idx < 320 then 2 else 2) else 3) else (if idx < 323 then 2 else 3)))) else (if idx < 335 then (if idx < 330 then (if idx < 327 then (if idx < 326 then (if idx < 325 then 2 else 3) else 3) else (if idx < 329 then (if idx < 328 then 3 else 3) else 3)) else (if idx < 333 then (if idx < 332 then (if idx < 331 then 2 else 1) else 3) else (if idx < 334 then 2 else 3))) else (if idx < 340 then (if idx < 338 then (if idx < 337 then (if idx < 336 then 2 else 3) else 1) else (if idx < 339 then 2 else 2)) else (if idx < 343 then (if idx < 342 then (if idx < 341 then 3 else 3) else 3) else (if idx < 344 then 3 else 3))))))))

def canonProf4At (c k : Nat) : Nat :=
  let idx := c * 15 + k
  (if idx < 180 then (if idx < 90 then (if idx < 45 then (if idx < 23 then (if idx < 12 then (if idx < 6 then (if idx < 3 then (if idx < 2 then (if idx < 1 then 52 else 52) else 104) else (if idx < 5 then (if idx < 4 then 52 else 104) else 104)) else (if idx < 9 then (if idx < 8 then (if idx < 7 then 156 else 52) else 104) else (if idx < 11 then (if idx < 10 then 104 else 156) else 104))) else (if idx < 18 then (if idx < 15 then (if idx < 14 then (if idx < 13 then 156 else 156) else 208) else (if idx < 17 then (if idx < 16 then 52 else 52) else 104)) else (if idx < 21 then (if idx < 20 then (if idx < 19 then 52 else 104) else 104) else (if idx < 22 then 156 else 64)))) else (if idx < 34 then (if idx < 29 then (if idx < 26 then (if idx < 25 then (if idx < 24 then 96 else 116) else 148) else (if idx < 28 then (if idx < 27 then 116 else 148) else 162)) else (if idx < 32 then (if idx < 31 then (if idx < 30 then 182 else 52) else 52) else (if idx < 33 then 104 else 52))) else (if idx < 40 then (if idx < 37 then (if idx < 36 then (if idx < 35 then 104 else 104) else 156) else (if idx < 39 then (if idx < 38 then 64 else 96) else 116)) else (if idx < 43 then (if idx < 42 then (if idx < 41 then 148 else 116) else 148) else (if idx < 44 then 162 else 194))))) else (if idx < 68 then (if idx < 57 then (if idx < 51 then (if idx < 48 then (if idx < 47 then (if idx < 46 then 52 else 52) else 104) else (if idx < 50 then (if idx < 49 then 52 else 104) else 104)) else (if idx < 54 then (if idx < 53 then (if idx < 52 then 156 else 64) else 116) else (if idx < 56 then (if idx < 55 then 116 else 162) else 116))) else (if idx < 63 then (if idx < 60 then (if idx < 59 then (if idx < 58 then 162 else 162) else 188) else (if idx < 62 then (if idx < 61 then 52 else 52) else 104)) else (if idx < 66 then (if idx < 65 then (if idx < 64 then 52 else 104) else 104) else (if idx < 67 then 156 else 64)))) else (if idx < 79 then (if idx < 74 then (if idx < 71 then (if idx < 70 then (if idx < 69 then 116 else 116) else 162) else (if idx < 73 then (if idx < 72 then 116 else 162) else 162)) else (if idx < 77 then (if idx < 76 then (if idx < 75 then 208 else 52) else 52) else (if idx < 78 then 104 else 52))) else (if idx < 85 then (if idx < 82 then (if idx < 81 then (if idx < 80 then 104 else 104) else 156) else (if idx < 84 then (if idx < 83 then 128 else 160) else 160)) else (if idx < 88 then (if idx < 87 then (if idx < 86 then 192 else 160) else 192) else (if idx < 89 then 192 else 208)))))) else (if idx < 135 then (if idx < 113 then (if idx < 102 then (if idx < 96 then (if idx < 93 then (if idx < 92 then (if idx < 91 then 52 else 52) else 104) else (if idx < 95 then (if idx < 94 then 52 else 104) else 104)) else (if idx < 99 then (if idx < 98 then (if idx < 97 then 156 else 128) else 160) else (if idx < 101 then (if idx < 100 then 160 else 192) else 160))) else (if idx < 108 then (if idx < 105 then (if idx < 104 then (if idx < 103 then 192 else 192) else 224) else (if idx < 107 then (if idx < 106 then 52 else 52) else 104)) else (if idx < 111 then (if idx < 110 then (if idx < 109 then 64 else 96) else 116) else (if idx < 112 then 148 else 64)))) else (if idx < 124 then (if idx < 119 then (if idx < 116 then (if idx < 115 then (if idx < 114 then 96 else 116) else 148) else (if idx < 118 then (if idx < 117 then 128 else 128) else 180)) else (if idx < 122 then (if idx < 121 then (if idx < 120 then 180 else 52) else 52) else (if idx < 123 then 104 else 64))) else (if idx < 130 then (if idx < 127 then (if idx < 126 then (if idx < 125 then 96 else 116) else 148) else (if idx < 129 then (if idx < 128 then 64 else 116) else 96)) else (if idx < 133 then (if idx < 132 then (if idx < 131 then 148 else 128) else 160) else (if idx < 134 then 160 else 192))))) else (if idx < 158 then (if idx < 147 then (if idx < 141 then (if idx < 138 then (if idx < 137 then (if idx < 136 then 52 else 52) else 104) else (if idx < 140 then (if idx < 139 then 64 else 96) else 116)) else (if idx < 144 then (if idx < 143 then (if idx < 142 then 148 else 64) else 116) else (if idx < 146 then (if idx < 145 then 116 else 162) else 128))) else (if idx < 153 then (if idx < 150 then (if idx < 149 then (if idx < 148 then 160 else 160) else 192) else (if idx < 152 then (if idx < 151 then 52 else 52) else 104)) else (if idx < 156 then (if idx < 155 then (if idx < 154 then 64 else 96) else 116) else (if idx < 157 then 148 else 64)))) else (if idx < 169 then (if idx < 164 then (if idx < 161 then (if idx < 160 then (if idx < 159 then 116 else 116) else 162) else (if idx < 163 then (if idx < 162 then 128 else 160) else 180)) else (if idx < 167 then (if idx < 166 then (if idx < 165 then 201 else 52) else 52) else (if idx < 168 then 104 else 64))) else (if idx < 175 then (if idx < 172 then (if idx < 171 then (if idx < 170 then 116 else 116) else 162) else (if idx < 174 then (if idx < 173 then 64 else 116) else 116)) else (if idx < 178 then (if idx < 177 then (if idx < 176 then 162 else 128) else 160) else (if idx < 179 then 160 else 192))))))) else (if idx < 270 then (if idx < 225 then (if idx < 203 then (if idx < 192 then (if idx < 186 then (if idx < 183 then (if idx < 182 then (if idx < 181 then 52 else 52) else 104) else (if idx < 185 then (if idx < 184 then 64 else 116) else 116)) else (if idx < 189 then (if idx < 188 then (if idx < 187 then 162 else 64) else 116) else (if idx < 191 then (if idx < 190 then 116 else 162) else 128))) else (if idx < 198 then (if idx < 195 then (if idx < 194 then (if idx < 193 then 180 else 180) else 210) else (if idx < 197 then (if idx < 196 then 52 else 52) else 104)) else (if idx < 201 then (if idx < 200 then (if idx < 199 then 64 else 116) else 116) else (if idx < 202 then 162 else 64)))) else (if idx < 214 then (if idx < 209 then (if idx < 206 then (if idx < 205 then (if idx < 204 then 116 else 116) else 162) else (if idx < 208 then (if idx < 207 then 128 else 180) else 180)) else (if idx < 212 then (if idx < 211 then (if idx < 210 then 214 else 52) else 52) else (if idx < 213 then 104 else 128))) else (if idx < 220 then (if idx < 217 then (if idx < 216 then (if idx < 215 then 160 else 160) else 192) else (if idx < 219 then (if idx < 218 then 128 else 160) else 160)) else (if idx < 223 then (if idx < 222 then (if idx < 221 then 192 else 256) else 256) else (if idx < 224 then 256 else 256))))) else (if idx < 248 then (if idx < 237 then (if idx < 231 then (if idx < 228 then (if idx < 227 then (if idx < 226 then 52 else 64) else 96) else (if idx < 230 then (if idx < 229 then 64 else 96) else 128)) else (if idx < 234 then (if idx < 233 then (if idx < 232 then 128 else 64) else 116) else (if idx < 236 then (if idx < 235 then 128 else 160) else 128))) else (if idx < 243 then (if idx < 240 then (if idx < 239 then (if idx < 238 then 160 else 192) else 192) else (if idx < 242 then (if idx < 241 then 52 else 64) else 96)) else (if idx < 246 then (if idx < 245 then (if idx < 244 then 64 else 116) else 128) else (if idx < 247 then 160 else 64)))) else (if idx < 259 then (if idx < 254 then (if idx < 251 then (if idx < 250 then (if idx < 249 then 116 else 128) else 160) else (if idx < 253 then (if idx < 252 then 128 else 160) else 128)) else (if idx < 257 then (if idx < 256 then (if idx < 255 then 160 else 52) else 64) else (if idx < 258 then 96 else 64))) else (if idx < 265 then (if idx < 262 then (if idx < 261 then (if idx < 260 then 116 else 128) else 160) else (if idx < 264 then (if idx < 263 then 64 else 116) else 128)) else (if idx < 268 then (if idx < 267 then (if idx < 266 then 160 else 128) else 160) else (if idx < 269 then 192 else 192)))))) else (if idx < 315 then (if idx < 293 then (if idx < 282 then (if idx < 276 then (if idx < 273 then (if idx < 272 then (if idx < 271 then 52 else 64) else 96) else (if idx < 275 then (if idx < 274 then 64 else 116) else 128)) else (if idx < 279 then (if idx < 278 then (if idx < 277 then 160 else 64) else 116) else (if idx < 281 then (if idx < 280 then 128 else 160) else 128))) else (if idx < 288 then (if idx < 285 then (if idx < 284 then (if idx < 283 then 180 else 192) else 224) else (if idx < 287 then (if idx < 286 then 52 else 64) else 116)) else (if idx < 291 then (if idx < 290 then (if idx < 289 then 64 else 116) else 128) else (if idx < 292 then 160 else 64)))) else (if idx < 304 then (if idx < 299 then (if idx < 296 then (if idx < 295 then (if idx < 294 then 116 else 128) else 160) else (if idx < 298 then (if idx < 297 then 128 else 160) else 128)) else (if idx < 302 then (if idx < 301 then (if idx < 300 then 160 else 52) else 64) else (if idx < 303 then 116 else 64))) else (if idx < 310 then (if idx < 307 then (if idx < 306 then (if idx < 305 then 116 else 128) else 160) else (if idx < 309 then (if idx < 308 then 64 else 116) else 128)) else (if idx < 313 then (if idx < 312 then (if idx < 311 then 180 else 128) else 180) else (if idx < 314 then 192 else 224))))) else (if idx < 338 then (if idx < 327 then (if idx < 321 then (if idx < 318 then (if idx < 317 then (if idx < 316 then 64 else 64) else 128) else (if idx < 320 then (if idx < 319 then 64 else 128) else 128)) else (if idx < 324 then (if idx < 323 then (if idx < 322 then 128 else 64) else 128) else (if idx < 326 then (if idx < 325 then 128 else 128) else 128))) else (if idx < 333 then (if idx < 330 then (if idx < 329 then (if idx < 328 then 128 else 128) else 128) else (if idx < 332 then (if idx < 331 then 64 else 64) else 128)) else (if idx < 336 then (if idx < 335 then (if idx < 334 then 64 else 128) else 128) else (if idx < 337 then 128 else 64)))) else (if idx < 349 then (if idx < 344 then (if idx < 341 then (if idx < 340 then (if idx < 339 then 128 else 128) else 192) else (if idx < 343 then (if idx < 342 then 128 else 192) else 192)) else (if idx < 347 then (if idx < 346 then (if idx < 345 then 192 else 64) else 64) else (if idx < 348 then 128 else 64))) else (if idx < 355 then (if idx < 352 then (if idx < 351 then (if idx < 350 then 128 else 128) else 192) else (if idx < 354 then (if idx < 353 then 64 else 128) else 128)) else (if idx < 358 then (if idx < 357 then (if idx < 356 then 192 else 128) else 192) else (if idx < 359 then 192 else 256))))))))

def perm4At (pi j : Nat) : Nat :=
  let idx := pi * 4 + j
  (if idx < 48 then (if idx < 24 then (if idx < 12 then (if idx < 6 then (if idx < 3 then (if idx < 2 then (if idx < 1 then 0 else 1) else 2) else (if idx < 5 then (if idx < 4 then 3 else 0) else 1)) else (if idx < 9 then (if idx < 8 then (if idx < 7 then 3 else 2) else 0) else (if idx < 11 then (if idx < 10 then 2 else 1) else 3))) else (if idx < 18 then (if idx < 15 then (if idx < 14 then (if idx < 13 then 0 else 2) else 3) else (if idx < 17 then (if idx < 16 then 1 else 0) else 3)) else (if idx < 21 then (if idx < 20 then (if idx < 19 then 1 else 2) else 0) else (if idx < 23 then (if idx < 22 then 3 else 2) else 1)))) else (if idx < 36 then (if idx < 30 then (if idx < 27 then (if idx < 26 then (if idx < 25 then 1 else 0) else 2) else (if idx < 29 then (if idx < 28 then 3 else 1) else 0)) else (if idx < 33 then (if idx < 32 then (if idx < 31 then 3 else 2) else 1) else (if idx < 35 then (if idx < 34 then 2 else 0) else 3))) else (if idx < 42 then (if idx < 39 then (if idx < 38 then (if idx < 37 then 1 else 2) else 3) else (if idx < 41 then (if idx < 40 then 0 else 1) else 3)) else (if idx < 45 then (if idx < 44 then (if idx < 43 then 0 else 2) else 1) else (if idx < 47 then (if idx < 46 then 3 else 2) else 0))))) else (if idx < 72 then (if idx < 60 then (if idx < 54 then (if idx < 51 then (if idx < 50 then (if idx < 49 then 2 else 0) else 1) else (if idx < 53 then (if idx < 52 then 3 else 2) else 0)) else (if idx < 57 then (if idx < 56 then (if idx < 55 then 3 else 1) else 2) else (if idx < 59 then (if idx < 58 then 1 else 0) else 3))) else (if idx < 66 then (if idx < 63 then (if idx < 62 then (if idx < 61 then 2 else 1) else 3) else (if idx < 65 then (if idx < 64 then 0 else 2) else 3)) else (if idx < 69 then (if idx < 68 then (if idx < 67 then 0 else 1) else 2) else (if idx < 71 then (if idx < 70 then 3 else 1) else 0)))) else (if idx < 84 then (if idx < 78 then (if idx < 75 then (if idx < 74 then (if idx < 73 then 3 else 0) else 1) else (if idx < 77 then (if idx < 76 then 2 else 3) else 0)) else (if idx < 81 then (if idx < 80 then (if idx < 79 then 2 else 1) else 3) else (if idx < 83 then (if idx < 82 then 1 else 0) else 2))) else (if idx < 90 then (if idx < 87 then (if idx < 86 then (if idx < 85 then 3 else 1) else 2) else (if idx < 89 then (if idx < 88 then 0 else 3) else 2)) else (if idx < 93 then (if idx < 92 then (if idx < 91 then 0 else 1) else 3) else (if idx < 95 then (if idx < 94 then 2 else 1) else 0))))))

def permMask4 (pi m : Nat) : Nat :=
  let b0 := if (m &&& 1) != 0 then (1 <<< perm4At pi 0) else 0
  let b1 := if (m &&& 2) != 0 then (1 <<< perm4At pi 1) else 0
  let b2 := if (m &&& 4) != 0 then (1 <<< perm4At pi 2) else 0
  let b3 := if (m &&& 8) != 0 then (1 <<< perm4At pi 3) else 0
  b0 ||| b1 ||| b2 ||| b3

/-- Kernel-certified exact F_2 / F_3 rank verification of all 23 linear rays (`23 × 15 = 345` ranks). -/
def checkLinRay4Exact : Bool :=
  allBelow 23 fun r =>
    let spec := linRay4Spec.getD r (2, [])
    allBelow 15 fun k =>
      subspaceRank4 spec.1 spec.2 (k + 1) == linRay4At r k

theorem checkLinRay4Exact_ok : checkLinRay4Exact = true := by decide

/-- Exact nonnegative integer decomposition `(rayIdx, weight3)` at common denominator `3`
    for all 24 canonical 4-marginal profiles of `h_uncond`. -/
def canonDecomp4 : List (List (Nat × Nat)) := [

  [(0, 156), (1, 156), (3, 156), (6, 156)],
  [(0, 78), (1, 102), (3, 102), (5, 18), (6, 60), (7, 60), (16, 36)],
  [(0, 114), (1, 138), (3, 138), (5, 18), (6, 96), (7, 60)],
  [(0, 96), (1, 78), (3, 78), (6, 78), (16, 60), (17, 18)],
  [(0, 156), (1, 138), (3, 138), (6, 138), (17, 18)],
  [(0, 156), (1, 48), (2, 60), (3, 48), (4, 60), (6, 48), (7, 60), (16, 48)],
  [(0, 204), (1, 96), (2, 60), (3, 96), (4, 60), (6, 96), (7, 60)],
  [(0, 96), (1, 96), (3, 156), (7, 60), (8, 60), (9, 36)],
  [(0, 132), (1, 132), (3, 96), (4, 60), (6, 96), (8, 60)],
  [(0, 132), (1, 90), (3, 96), (5, 42), (6, 96), (8, 42), (13, 18)],
  [(0, 159), (1, 117), (3, 123), (6, 63), (8, 60), (12, 18), (16, 15)],
  [(0, 90), (1, 90), (3, 96), (5, 24), (6, 96), (9, 24), (17, 18), (18, 18)],
  [(0, 144), (1, 144), (3, 90), (6, 90), (12, 18), (14, 18), (16, 30)],
  [(0, 156), (1, 156), (3, 102), (6, 102), (12, 18), (14, 18), (16, 18)],
  [(0, 192), (1, 192), (5, 36), (9, 36), (19, 20), (20, 20), (21, 20), (22, 20)],
  [(0, 192), (1, 96), (3, 96), (8, 60), (10, 60), (14, 36)],
  [(5, 132), (6, 96), (11, 60)],
  [(0, 96), (1, 96), (3, 96), (9, 60), (10, 60), (16, 36)],
  [(0, 192), (1, 192), (3, 132), (6, 96), (10, 60)],
  [(5, 132), (6, 96), (15, 60)],
  [(0, 192), (1, 132), (3, 132), (6, 96), (14, 60)],
  [(15, 192)],
  [(0, 192), (14, 192)],
  [(0, 192), (1, 192), (3, 192), (6, 192)]
]

def sumDecomp4 (terms : List (Nat × Nat)) (k : Nat) : Nat :=
  terms.foldl (fun acc tw => acc + tw.2 * linRay4At tw.1 k) 0

def checkCanonDecomp4 : Bool :=
  allBelow 24 fun p =>
    let terms := canonDecomp4.getD p []
    allBelow 15 fun k =>
      3 * canonProf4At p k == sumDecomp4 terms k

theorem checkCanonDecomp4_ok : checkCanonDecomp4 = true := by decide

/-- 4-marginal of `hUncond` on four 12-bit variable masks. -/
def hUncondMarg4 (m0 m1 m2 m3 mask : Nat) : Nat :=
  let u0 := if (mask &&& 1) != 0 then m0 else 0
  let u1 := if (mask &&& 2) != 0 then m1 else 0
  let u2 := if (mask &&& 4) != 0 then m2 else 0
  let u3 := if (mask &&& 8) != 0 then m3 else 0
  hUncond (u0 ||| u1 ||| u2 ||| u3)

/-- The 6 retrieval objects `{W1, W2, A0, A1, A2, A3}` as 12-bit masks. -/
def retObjMask (j : Nat) : Nat :=
  match j with
  | 0 => 15
  | 1 => 240
  | 2 => 256
  | 3 => 512
  | 4 => 1024
  | _ => 2048

def sing495Quad (idx : Nat) : Nat :=
  (if idx < 248 then (if idx < 124 then (if idx < 62 then (if idx < 31 then (if idx < 16 then (if idx < 8 then (if idx < 4 then (if idx < 2 then (if idx < 1 then 291 else 292) else (if idx < 3 then 293 else 294)) else (if idx < 6 then (if idx < 5 then 295 else 296) else (if idx < 7 then 297 else 298))) else (if idx < 12 then (if idx < 10 then (if idx < 9 then 299 else 308) else (if idx < 11 then 309 else 310)) else (if idx < 14 then (if idx < 13 then 311 else 312) else (if idx < 15 then 313 else 314)))) else (if idx < 24 then (if idx < 20 then (if idx < 18 then (if idx < 17 then 315 else 325) else (if idx < 19 then 326 else 327)) else (if idx < 22 then (if idx < 21 then 328 else 329) else (if idx < 23 then 330 else 331))) else (if idx < 28 then (if idx < 26 then (if idx < 25 then 342 else 343) else (if idx < 27 then 344 else 345)) else (if idx < 30 then (if idx < 29 then 346 else 347) else 359)))) else (if idx < 47 then (if idx < 39 then (if idx < 35 then (if idx < 33 then (if idx < 32 then 360 else 361) else (if idx < 34 then 362 else 363)) else (if idx < 37 then (if idx < 36 then 376 else 377) else (if idx < 38 then 378 else 379))) else (if idx < 43 then (if idx < 41 then (if idx < 40 then 393 else 394) else (if idx < 42 then 395 else 410)) else (if idx < 45 then (if idx < 44 then 411 else 427) else (if idx < 46 then 564 else 565)))) else (if idx < 55 then (if idx < 51 then (if idx < 49 then (if idx < 48 then 566 else 567) else (if idx < 50 then 568 else 569)) else (if idx < 53 then (if idx < 52 then 570 else 571) else (if idx < 54 then 581 else 582))) else (if idx < 59 then (if idx < 57 then (if idx < 56 then 583 else 584) else (if idx < 58 then 585 else 586)) else (if idx < 61 then (if idx < 60 then 587 else 598) else 599))))) else (if idx < 93 then (if idx < 78 then (if idx < 70 then (if idx < 66 then (if idx < 64 then (if idx < 63 then 600 else 601) else (if idx < 65 then 602 else 603)) else (if idx < 68 then (if idx < 67 then 615 else 616) else (if idx < 69 then 617 else 618))) else (if idx < 74 then (if idx < 72 then (if idx < 71 then 619 else 632) else (if idx < 73 then 633 else 634)) else (if idx < 76 then (if idx < 75 then 635 else 649) else (if idx < 77 then 650 else 651)))) else (if idx < 86 then (if idx < 82 then (if idx < 80 then (if idx < 79 then 666 else 667) else (if idx < 81 then 683 else 837)) else (if idx < 84 then (if idx < 83 then 838 else 839) else (if idx < 85 then 840 else 841))) else (if idx < 90 then (if idx < 88 then (if idx < 87 then 842 else 843) else (if idx < 89 then 854 else 855)) else (if idx < 92 then (if idx < 91 then 856 else 857) else 858)))) else (if idx < 109 then (if idx < 101 then (if idx < 97 then (if idx < 95 then (if idx < 94 then 859 else 871) else (if idx < 96 then 872 else 873)) else (if idx < 99 then (if idx < 98 then 874 else 875) else (if idx < 100 then 888 else 889))) else (if idx < 105 then (if idx < 103 then (if idx < 102 then 890 else 891) else (if idx < 104 then 905 else 906)) else (if idx < 107 then (if idx < 106 then 907 else 922) else (if idx < 108 then 923 else 939)))) else (if idx < 117 then (if idx < 113 then (if idx < 111 then (if idx < 110 then 1110 else 1111) else (if idx < 112 then 1112 else 1113)) else (if idx < 115 then (if idx < 114 then 1114 else 1115) else (if idx < 116 then 1127 else 1128))) else (if idx < 121 then (if idx < 119 then (if idx < 118 then 1129 else 1130) else (if idx < 120 then 1131 else 1144)) else (if idx < 123 then (if idx < 122 then 1145 else 1146) else 1147)))))) else (if idx < 186 then (if idx < 155 then (if idx < 140 then (if idx < 132 then (if idx < 128 then (if idx < 126 then (if idx < 125 then 1161 else 1162) else (if idx < 127 then 1163 else 1178)) else (if idx < 130 then (if idx < 129 then 1179 else 1195) else (if idx < 131 then 1383 else 1384))) else (if idx < 136 then (if idx < 134 then (if idx < 133 then 1385 else 1386) else (if idx < 135 then 1387 else 1400)) else (if idx < 138 then (if idx < 137 then 1401 else 1402) else (if idx < 139 then 1403 else 1417)))) else (if idx < 148 then (if idx < 144 then (if idx < 142 then (if idx < 141 then 1418 else 1419) else (if idx < 143 then 1434 else 1435)) else (if idx < 146 then (if idx < 145 then 1451 else 1656) else (if idx < 147 then 1657 else 1658))) else (if idx < 152 then (if idx < 150 then (if idx < 149 then 1659 else 1673) else (if idx < 151 then 1674 else 1675)) else (if idx < 154 then (if idx < 153 then 1690 else 1691) else 1707)))) else (if idx < 171 then (if idx < 163 then (if idx < 159 then (if idx < 157 then (if idx < 156 then 1929 else 1930) else (if idx < 158 then 1931 else 1946)) else (if idx < 161 then (if idx < 160 then 1947 else 1963) else (if idx < 162 then 2202 else 2203))) else (if idx < 167 then (if idx < 165 then (if idx < 164 then 2219 else 2475) else (if idx < 166 then 4660 else 4661)) else (if idx < 169 then (if idx < 168 then 4662 else 4663) else (if idx < 170 then 4664 else 4665)))) else (if idx < 179 then (if idx < 175 then (if idx < 173 then (if idx < 172 then 4666 else 4667) else (if idx < 174 then 4677 else 4678)) else (if idx < 177 then (if idx < 176 then 4679 else 4680) else (if idx < 178 then 4681 else 4682))) else (if idx < 183 then (if idx < 181 then (if idx < 180 then 4683 else 4694) else (if idx < 182 then 4695 else 4696)) else (if idx < 185 then (if idx < 184 then 4697 else 4698) else 4699))))) else (if idx < 217 then (if idx < 202 then (if idx < 194 then (if idx < 190 then (if idx < 188 then (if idx < 187 then 4711 else 4712) else (if idx < 189 then 4713 else 4714)) else (if idx < 192 then (if idx < 191 then 4715 else 4728) else (if idx < 193 then 4729 else 4730))) else (if idx < 198 then (if idx < 196 then (if idx < 195 then 4731 else 4745) else (if idx < 197 then 4746 else 4747)) else (if idx < 200 then (if idx < 199 then 4762 else 4763) else (if idx < 201 then 4779 else 4933)))) else (if idx < 210 then (if idx < 206 then (if idx < 204 then (if idx < 203 then 4934 else 4935) else (if idx < 205 then 4936 else 4937)) else (if idx < 208 then (if idx < 207 then 4938 else 4939) else (if idx < 209 then 4950 else 4951))) else (if idx < 214 then (if idx < 212 then (if idx < 211 then 4952 else 4953) else (if idx < 213 then 4954 else 4955)) else (if idx < 216 then (if idx < 215 then 4967 else 4968) else 4969)))) else (if idx < 233 then (if idx < 225 then (if idx < 221 then (if idx < 219 then (if idx < 218 then 4970 else 4971) else (if idx < 220 then 4984 else 4985)) else (if idx < 223 then (if idx < 222 then 4986 else 4987) else (if idx < 224 then 5001 else 5002))) else (if idx < 229 then (if idx < 227 then (if idx < 226 then 5003 else 5018) else (if idx < 228 then 5019 else 5035)) else (if idx < 231 then (if idx < 230 then 5206 else 5207) else (if idx < 232 then 5208 else 5209)))) else (if idx < 241 then (if idx < 237 then (if idx < 235 then (if idx < 234 then 5210 else 5211) else (if idx < 236 then 5223 else 5224)) else (if idx < 239 then (if idx < 238 then 5225 else 5226) else (if idx < 240 then 5227 else 5240))) else (if idx < 245 then (if idx < 243 then (if idx < 242 then 5241 else 5242) else (if idx < 244 then 5243 else 5257)) else (if idx < 247 then (if idx < 246 then 5258 else 5259) else 5274))))))) else (if idx < 372 then (if idx < 310 then (if idx < 279 then (if idx < 264 then (if idx < 256 then (if idx < 252 then (if idx < 250 then (if idx < 249 then 5275 else 5291) else (if idx < 251 then 5479 else 5480)) else (if idx < 254 then (if idx < 253 then 5481 else 5482) else (if idx < 255 then 5483 else 5496))) else (if idx < 260 then (if idx < 258 then (if idx < 257 then 5497 else 5498) else (if idx < 259 then 5499 else 5513)) else (if idx < 262 then (if idx < 261 then 5514 else 5515) else (if idx < 263 then 5530 else 5531)))) else (if idx < 272 then (if idx < 268 then (if idx < 266 then (if idx < 265 then 5547 else 5752) else (if idx < 267 then 5753 else 5754)) else (if idx < 270 then (if idx < 269 then 5755 else 5769) else (if idx < 271 then 5770 else 5771))) else (if idx < 276 then (if idx < 274 then (if idx < 273 then 5786 else 5787) else (if idx < 275 then 5803 else 6025)) else (if idx < 278 then (if idx < 277 then 6026 else 6027) else 6042)))) else (if idx < 295 then (if idx < 287 then (if idx < 283 then (if idx < 281 then (if idx < 280 then 6043 else 6059) else (if idx < 282 then 6298 else 6299)) else (if idx < 285 then (if idx < 284 then 6315 else 6571) else (if idx < 286 then 9029 else 9030))) else (if idx < 291 then (if idx < 289 then (if idx < 288 then 9031 else 9032) else (if idx < 290 then 9033 else 9034)) else (if idx < 293 then (if idx < 292 then 9035 else 9046) else (if idx < 294 then 9047 else 9048)))) else (if idx < 303 then (if idx < 299 then (if idx < 297 then (if idx < 296 then 9049 else 9050) else (if idx < 298 then 9051 else 9063)) else (if idx < 301 then (if idx < 300 then 9064 else 9065) else (if idx < 302 then 9066 else 9067))) else (if idx < 307 then (if idx < 305 then (if idx < 304 then 9080 else 9081) else (if idx < 306 then 9082 else 9083)) else (if idx < 309 then (if idx < 308 then 9097 else 9098) else 9099))))) else (if idx < 341 then (if idx < 326 then (if idx < 318 then (if idx < 314 then (if idx < 312 then (if idx < 311 then 9114 else 9115) else (if idx < 313 then 9131 else 9302)) else (if idx < 316 then (if idx < 315 then 9303 else 9304) else (if idx < 317 then 9305 else 9306))) else (if idx < 322 then (if idx < 320 then (if idx < 319 then 9307 else 9319) else (if idx < 321 then 9320 else 9321)) else (if idx < 324 then (if idx < 323 then 9322 else 9323) else (if idx < 325 then 9336 else 9337)))) else (if idx < 334 then (if idx < 330 then (if idx < 328 then (if idx < 327 then 9338 else 9339) else (if idx < 329 then 9353 else 9354)) else (if idx < 332 then (if idx < 331 then 9355 else 9370) else (if idx < 333 then 9371 else 9387))) else (if idx < 338 then (if idx < 336 then (if idx < 335 then 9575 else 9576) else (if idx < 337 then 9577 else 9578)) else (if idx < 340 then (if idx < 339 then 9579 else 9592) else 9593)))) else (if idx < 357 then (if idx < 349 then (if idx < 345 then (if idx < 343 then (if idx < 342 then 9594 else 9595) else (if idx < 344 then 9609 else 9610)) else (if idx < 347 then (if idx < 346 then 9611 else 9626) else (if idx < 348 then 9627 else 9643))) else (if idx < 353 then (if idx < 351 then (if idx < 350 then 9848 else 9849) else (if idx < 352 then 9850 else 9851)) else (if idx < 355 then (if idx < 354 then 9865 else 9866) else (if idx < 356 then 9867 else 9882)))) else (if idx < 365 then (if idx < 361 then (if idx < 359 then (if idx < 358 then 9883 else 9899) else (if idx < 360 then 10121 else 10122)) else (if idx < 363 then (if idx < 362 then 10123 else 10138) else (if idx < 364 then 10139 else 10155))) else (if idx < 369 then (if idx < 367 then (if idx < 366 then 10394 else 10395) else (if idx < 368 then 10411 else 10667)) else (if idx < 371 then (if idx < 370 then 13398 else 13399) else 13400)))))) else (if idx < 434 then (if idx < 403 then (if idx < 388 then (if idx < 380 then (if idx < 376 then (if idx < 374 then (if idx < 373 then 13401 else 13402) else (if idx < 375 then 13403 else 13415)) else (if idx < 378 then (if idx < 377 then 13416 else 13417) else (if idx < 379 then 13418 else 13419))) else (if idx < 384 then (if idx < 382 then (if idx < 381 then 13432 else 13433) else (if idx < 383 then 13434 else 13435)) else (if idx < 386 then (if idx < 385 then 13449 else 13450) else (if idx < 387 then 13451 else 13466)))) else (if idx < 396 then (if idx < 392 then (if idx < 390 then (if idx < 389 then 13467 else 13483) else (if idx < 391 then 13671 else 13672)) else (if idx < 394 then (if idx < 393 then 13673 else 13674) else (if idx < 395 then 13675 else 13688))) else (if idx < 400 then (if idx < 398 then (if idx < 397 then 13689 else 13690) else (if idx < 399 then 13691 else 13705)) else (if idx < 402 then (if idx < 401 then 13706 else 13707) else 13722)))) else (if idx < 419 then (if idx < 411 then (if idx < 407 then (if idx < 405 then (if idx < 404 then 13723 else 13739) else (if idx < 406 then 13944 else 13945)) else (if idx < 409 then (if idx < 408 then 13946 else 13947) else (if idx < 410 then 13961 else 13962))) else (if idx < 415 then (if idx < 413 then (if idx < 412 then 13963 else 13978) else (if idx < 414 then 13979 else 13995)) else (if idx < 417 then (if idx < 416 then 14217 else 14218) else (if idx < 418 then 14219 else 14234)))) else (if idx < 427 then (if idx < 423 then (if idx < 421 then (if idx < 420 then 14235 else 14251) else (if idx < 422 then 14490 else 14491)) else (if idx < 425 then (if idx < 424 then 14507 else 14763) else (if idx < 426 then 17767 else 17768))) else (if idx < 431 then (if idx < 429 then (if idx < 428 then 17769 else 17770) else (if idx < 430 then 17771 else 17784)) else (if idx < 433 then (if idx < 432 then 17785 else 17786) else 17787))))) else (if idx < 465 then (if idx < 450 then (if idx < 442 then (if idx < 438 then (if idx < 436 then (if idx < 435 then 17801 else 17802) else (if idx < 437 then 17803 else 17818)) else (if idx < 440 then (if idx < 439 then 17819 else 17835) else (if idx < 441 then 18040 else 18041))) else (if idx < 446 then (if idx < 444 then (if idx < 443 then 18042 else 18043) else (if idx < 445 then 18057 else 18058)) else (if idx < 448 then (if idx < 447 then 18059 else 18074) else (if idx < 449 then 18075 else 18091)))) else (if idx < 458 then (if idx < 454 then (if idx < 452 then (if idx < 451 then 18313 else 18314) else (if idx < 453 then 18315 else 18330)) else (if idx < 456 then (if idx < 455 then 18331 else 18347) else (if idx < 457 then 18586 else 18587))) else (if idx < 462 then (if idx < 460 then (if idx < 459 then 18603 else 18859) else (if idx < 461 then 22136 else 22137)) else (if idx < 464 then (if idx < 463 then 22138 else 22139) else 22153)))) else (if idx < 480 then (if idx < 473 then (if idx < 469 then (if idx < 467 then (if idx < 466 then 22154 else 22155) else (if idx < 468 then 22170 else 22171)) else (if idx < 471 then (if idx < 470 then 22187 else 22409) else (if idx < 472 then 22410 else 22411))) else (if idx < 477 then (if idx < 475 then (if idx < 474 then 22426 else 22427) else (if idx < 476 then 22443 else 22682)) else (if idx < 479 then (if idx < 478 then 22683 else 22699) else 22955))) else (if idx < 488 then (if idx < 484 then (if idx < 482 then (if idx < 481 then 26505 else 26506) else (if idx < 483 then 26507 else 26522)) else (if idx < 486 then (if idx < 485 then 26523 else 26539) else (if idx < 487 then 26778 else 26779))) else (if idx < 492 then (if idx < 490 then (if idx < 489 then 26795 else 27051) else (if idx < 491 then 30874 else 30875)) else (if idx < 494 then (if idx < 493 then 30891 else 31147) else 35243))))))))

def sing495Cert (idx : Nat) : Nat :=
  (if idx < 248 then (if idx < 124 then (if idx < 62 then (if idx < 31 then (if idx < 16 then (if idx < 8 then (if idx < 4 then (if idx < 2 then (if idx < 1 then 504 else 528) else (if idx < 3 then 528 else 528)) else (if idx < 6 then (if idx < 5 then 528 else 402) else (if idx < 7 then 404 else 406))) else (if idx < 12 then (if idx < 10 then (if idx < 9 then 474 else 528) else (if idx < 11 then 528 else 528)) else (if idx < 14 then (if idx < 13 then 528 else 402) else (if idx < 15 then 404 else 474)))) else (if idx < 24 then (if idx < 20 then (if idx < 18 then (if idx < 17 then 406 else 552) else (if idx < 19 then 552 else 552)) else (if idx < 22 then (if idx < 21 then 379 else 452) else (if idx < 23 then 498 else 498))) else (if idx < 28 then (if idx < 26 then (if idx < 25 then 552 else 552) else (if idx < 27 then 450 else 381)) else (if idx < 30 then (if idx < 29 then 498 else 498) else 552)))) else (if idx < 47 then (if idx < 39 then (if idx < 35 then (if idx < 33 then (if idx < 32 then 450 else 452) else (if idx < 34 then 430 else 498)) else (if idx < 37 then (if idx < 36 then 450 else 452) else (if idx < 38 then 498 else 430))) else (if idx < 43 then (if idx < 41 then (if idx < 40 then 208 else 232) else (if idx < 42 then 232 else 233)) else (if idx < 45 then (if idx < 44 then 233 else 280) else (if idx < 46 then 528 else 528)))) else (if idx < 55 then (if idx < 51 then (if idx < 49 then (if idx < 48 then 528 else 528) else (if idx < 50 then 402 else 474)) else (if idx < 53 then (if idx < 52 then 404 else 406) else (if idx < 54 then 552 else 552))) else (if idx < 59 then (if idx < 57 then (if idx < 56 then 552 else 379) else (if idx < 58 then 498 else 452)) else (if idx < 61 then (if idx < 60 then 498 else 552) else 552))))) else (if idx < 93 then (if idx < 78 then (if idx < 70 then (if idx < 66 then (if idx < 64 then (if idx < 63 then 450 else 430) else (if idx < 65 then 452 else 498)) else (if idx < 68 then (if idx < 67 then 552 else 450) else (if idx < 69 then 498 else 381))) else (if idx < 74 then (if idx < 72 then (if idx < 71 then 498 else 450) else (if idx < 73 then 498 else 452)) else (if idx < 76 then (if idx < 75 then 430 else 232) else (if idx < 77 then 208 else 232)))) else (if idx < 86 then (if idx < 82 then (if idx < 80 then (if idx < 79 then 239 else 280) else (if idx < 81 then 233 else 552)) else (if idx < 84 then (if idx < 83 then 552 else 552) else (if idx < 85 then 379 else 498))) else (if idx < 90 then (if idx < 88 then (if idx < 87 then 498 else 452) else (if idx < 89 then 552 else 552)) else (if idx < 92 then (if idx < 91 then 450 else 430) else 498)))) else (if idx < 109 then (if idx < 101 then (if idx < 97 then (if idx < 95 then (if idx < 94 then 452 else 552) else (if idx < 96 then 450 else 498)) else (if idx < 99 then (if idx < 98 then 430 else 452) else (if idx < 100 then 450 else 498))) else (if idx < 105 then (if idx < 103 then (if idx < 102 then 498 else 381) else (if idx < 104 then 232 else 232)) else (if idx < 107 then (if idx < 106 then 208 else 280) else (if idx < 108 then 239 else 239)))) else (if idx < 117 then (if idx < 113 then (if idx < 111 then (if idx < 110 then 537 else 537) else (if idx < 112 then 378 else 454)) else (if idx < 115 then (if idx < 114 then 501 else 501) else (if idx < 116 then 537 else 378))) else (if idx < 121 then (if idx < 119 then (if idx < 118 then 501 else 454) else (if idx < 120 then 501 else 378)) else (if idx < 123 then (if idx < 122 then 501 else 501) else 454)))))) else (if idx < 186 then (if idx < 155 then (if idx < 140 then (if idx < 132 then (if idx < 128 then (if idx < 126 then (if idx < 125 then 184 else 184) else (if idx < 127 then 184 else 328)) else (if idx < 130 then (if idx < 129 then 328 else 328) else (if idx < 131 then 537 else 426))) else (if idx < 136 then (if idx < 134 then (if idx < 133 then 452 else 454) else (if idx < 135 then 501 else 426)) else (if idx < 138 then (if idx < 137 then 452 else 501) else (if idx < 139 then 454 else 208)))) else (if idx < 148 then (if idx < 144 then (if idx < 142 then (if idx < 141 then 256 else 256) else (if idx < 143 then 257 else 257)) else (if idx < 146 then (if idx < 145 then 304 else 426) else (if idx < 147 then 501 else 452))) else (if idx < 152 then (if idx < 150 then (if idx < 149 then 454 else 256) else (if idx < 151 then 208 else 256)) else (if idx < 154 then (if idx < 153 then 263 else 304) else 257)))) else (if idx < 171 then (if idx < 163 then (if idx < 159 then (if idx < 157 then (if idx < 156 then 256 else 256) else (if idx < 158 then 208 else 304)) else (if idx < 161 then (if idx < 160 then 263 else 263) else (if idx < 162 then 33 else 33))) else (if idx < 167 then (if idx < 165 then (if idx < 164 then 33 else 81) else (if idx < 166 then 528 else 528)) else (if idx < 169 then (if idx < 168 then 528 else 528) else (if idx < 170 then 474 else 402)))) else (if idx < 179 then (if idx < 175 then (if idx < 173 then (if idx < 172 then 404 else 406) else (if idx < 174 then 552 else 552)) else (if idx < 177 then (if idx < 176 then 552 else 430) else (if idx < 178 then 450 else 452))) else (if idx < 183 then (if idx < 181 then (if idx < 180 then 498 else 552) else (if idx < 182 then 552 else 498)) else (if idx < 185 then (if idx < 184 then 379 else 452) else 498))))) else (if idx < 217 then (if idx < 202 then (if idx < 194 then (if idx < 190 then (if idx < 188 then (if idx < 187 then 552 else 498) else (if idx < 189 then 450 else 381)) else (if idx < 192 then (if idx < 191 then 498 else 498) else (if idx < 193 then 450 else 452))) else (if idx < 198 then (if idx < 196 then (if idx < 195 then 430 else 238) else (if idx < 197 then 239 else 280)) else (if idx < 200 then (if idx < 199 then 208 else 232) else (if idx < 201 then 233 else 552)))) else (if idx < 210 then (if idx < 206 then (if idx < 204 then (if idx < 203 then 552 else 552) else (if idx < 205 then 430 else 450)) else (if idx < 208 then (if idx < 207 then 498 else 452) else (if idx < 209 then 552 else 552))) else (if idx < 214 then (if idx < 212 then (if idx < 211 then 498 else 379) else (if idx < 213 then 498 else 452)) else (if idx < 216 then (if idx < 215 then 552 else 498) else 450)))) else (if idx < 233 then (if idx < 225 then (if idx < 221 then (if idx < 219 then (if idx < 218 then 430 else 452) else (if idx < 220 then 498 else 450)) else (if idx < 223 then (if idx < 222 then 498 else 381) else (if idx < 224 then 238 else 280))) else (if idx < 229 then (if idx < 227 then (if idx < 226 then 239 else 232) else (if idx < 228 then 208 else 239)) else (if idx < 231 then (if idx < 230 then 537 else 537) else (if idx < 232 then 452 else 379)))) else (if idx < 241 then (if idx < 237 then (if idx < 235 then (if idx < 234 then 501 else 501) else (if idx < 236 then 537 else 452)) else (if idx < 239 then (if idx < 238 then 426 else 454) else (if idx < 240 then 501 else 452))) else (if idx < 245 then (if idx < 243 then (if idx < 242 then 426 else 501) else (if idx < 244 then 454 else 209)) else (if idx < 247 then (if idx < 246 then 257 else 257) else 256))))))) else (if idx < 372 then (if idx < 310 then (if idx < 279 then (if idx < 264 then (if idx < 256 then (if idx < 252 then (if idx < 250 then (if idx < 249 then 256 else 304) else (if idx < 251 then 537 else 501)) else (if idx < 254 then (if idx < 253 then 378 else 454) else (if idx < 255 then 501 else 501))) else (if idx < 260 then (if idx < 258 then (if idx < 257 then 378 else 501) else (if idx < 259 then 454 else 190)) else (if idx < 262 then (if idx < 261 then 328 else 328) else (if idx < 263 then 184 else 184)))) else (if idx < 272 then (if idx < 268 then (if idx < 266 then (if idx < 265 then 328 else 501) else (if idx < 267 then 426 else 452)) else (if idx < 270 then (if idx < 269 then 454 else 262) else (if idx < 271 then 263 else 304))) else (if idx < 276 then (if idx < 274 then (if idx < 273 then 208 else 256) else (if idx < 275 then 257 else 262)) else (if idx < 278 then (if idx < 277 then 304 else 263) else 256)))) else (if idx < 295 then (if idx < 287 then (if idx < 283 then (if idx < 281 then (if idx < 280 then 208 else 263) else (if idx < 282 then 39 else 39)) else (if idx < 285 then (if idx < 284 then 81 else 33) else (if idx < 286 then 552 else 552))) else (if idx < 291 then (if idx < 289 then (if idx < 288 then 552 else 430) else (if idx < 290 then 498 else 450)) else (if idx < 293 then (if idx < 292 then 452 else 552) else (if idx < 294 then 552 else 498)))) else (if idx < 303 then (if idx < 299 then (if idx < 297 then (if idx < 296 then 430 else 450) else (if idx < 298 then 452 else 552)) else (if idx < 301 then (if idx < 300 then 498 else 498) else (if idx < 302 then 379 else 452))) else (if idx < 307 then (if idx < 305 then (if idx < 304 then 498 else 498) else (if idx < 306 then 450 else 381)) else (if idx < 309 then (if idx < 308 then 280 else 238) else 239))))) else (if idx < 341 then (if idx < 326 then (if idx < 318 then (if idx < 314 then (if idx < 312 then (if idx < 311 then 238 else 239) else (if idx < 313 then 208 else 537)) else (if idx < 316 then (if idx < 315 then 537 else 452) else (if idx < 317 then 454 else 426))) else (if idx < 322 then (if idx < 320 then (if idx < 319 then 501 else 537) else (if idx < 321 then 452 else 501)) else (if idx < 324 then (if idx < 323 then 379 else 501) else (if idx < 325 then 452 else 501)))) else (if idx < 334 then (if idx < 330 then (if idx < 328 then (if idx < 327 then 426 else 454) else (if idx < 329 then 257 else 209)) else (if idx < 332 then (if idx < 331 then 257 else 262) else (if idx < 333 then 304 else 256))) else (if idx < 338 then (if idx < 336 then (if idx < 335 then 537 else 501) else (if idx < 337 then 452 else 379)) else (if idx < 340 then (if idx < 339 then 501 else 501) else 452)))) else (if idx < 357 then (if idx < 349 then (if idx < 345 then (if idx < 343 then (if idx < 342 then 426 else 454) else (if idx < 344 then 263 else 262)) else (if idx < 347 then (if idx < 346 then 304 else 209) else (if idx < 348 then 257 else 256))) else (if idx < 353 then (if idx < 351 then (if idx < 350 then 501 else 501) else (if idx < 352 then 378 else 454)) else (if idx < 355 then (if idx < 354 then 328 else 190) else (if idx < 356 then 328 else 190)))) else (if idx < 365 then (if idx < 361 then (if idx < 359 then (if idx < 358 then 328 else 184) else (if idx < 360 then 304 else 262)) else (if idx < 363 then (if idx < 362 then 263 else 262) else (if idx < 364 then 263 else 208))) else (if idx < 369 then (if idx < 367 then (if idx < 366 then 45 else 81) else (if idx < 368 then 39 else 39)) else (if idx < 371 then (if idx < 370 then 537 else 537) else 452)))))) else (if idx < 434 then (if idx < 403 then (if idx < 388 then (if idx < 380 then (if idx < 376 then (if idx < 374 then (if idx < 373 then 454 else 501) else (if idx < 375 then 426 else 537)) else (if idx < 378 then (if idx < 377 then 452 else 501) else (if idx < 379 then 454 else 426))) else (if idx < 384 then (if idx < 382 then (if idx < 381 then 452 else 501) else (if idx < 383 then 501 else 379)) else (if idx < 386 then (if idx < 385 then 257 else 257) else (if idx < 387 then 209 else 304)))) else (if idx < 396 then (if idx < 392 then (if idx < 390 then (if idx < 389 then 262 else 262) else (if idx < 391 then 537 else 501)) else (if idx < 394 then (if idx < 393 then 452 else 454) else (if idx < 395 then 426 else 501))) else (if idx < 400 then (if idx < 398 then (if idx < 397 then 452 else 501) else (if idx < 399 then 379 else 263)) else (if idx < 402 then (if idx < 401 then 304 else 262) else 257)))) else (if idx < 419 then (if idx < 411 then (if idx < 407 then (if idx < 405 then (if idx < 404 then 209 else 262) else (if idx < 406 then 501 else 501)) else (if idx < 409 then (if idx < 408 then 452 else 379) else (if idx < 410 then 304 else 263))) else (if idx < 415 then (if idx < 413 then (if idx < 412 then 262 else 263) else (if idx < 414 then 262 else 209)) else (if idx < 417 then (if idx < 416 then 328 else 328) else (if idx < 418 then 190 else 328)))) else (if idx < 427 then (if idx < 423 then (if idx < 421 then (if idx < 420 then 190 else 190) else (if idx < 422 then 81 else 45)) else (if idx < 425 then (if idx < 424 then 45 else 45) else (if idx < 426 then 504 else 402))) else (if idx < 431 then (if idx < 429 then (if idx < 428 then 404 else 406) else (if idx < 430 then 474 else 402)) else (if idx < 433 then (if idx < 432 then 404 else 474) else 406))))) else (if idx < 465 then (if idx < 450 then (if idx < 442 then (if idx < 438 then (if idx < 436 then (if idx < 435 then 208 else 232) else (if idx < 437 then 232 else 233)) else (if idx < 440 then (if idx < 439 then 233 else 280) else (if idx < 441 then 402 else 474))) else (if idx < 446 then (if idx < 444 then (if idx < 443 then 404 else 406) else (if idx < 445 then 232 else 208)) else (if idx < 448 then (if idx < 447 then 232 else 239) else (if idx < 449 then 280 else 233)))) else (if idx < 458 then (if idx < 454 then (if idx < 452 then (if idx < 451 then 232 else 232) else (if idx < 453 then 208 else 280)) else (if idx < 456 then (if idx < 455 then 239 else 239) else (if idx < 457 then 57 else 57))) else (if idx < 462 then (if idx < 460 then (if idx < 459 then 57 else 105) else (if idx < 461 then 474 else 402)) else (if idx < 464 then (if idx < 463 then 404 else 406) else 238)))) else (if idx < 480 then (if idx < 473 then (if idx < 469 then (if idx < 467 then (if idx < 466 then 239 else 280) else (if idx < 468 then 208 else 232)) else (if idx < 471 then (if idx < 470 then 233 else 238) else (if idx < 472 then 280 else 239))) else (if idx < 477 then (if idx < 475 then (if idx < 474 then 232 else 208) else (if idx < 476 then 239 else 63)) else (if idx < 479 then (if idx < 478 then 63 else 105) else 57))) else (if idx < 488 then (if idx < 484 then (if idx < 482 then (if idx < 481 then 280 else 238) else (if idx < 483 then 239 else 238)) else (if idx < 486 then (if idx < 485 then 239 else 208) else (if idx < 487 then 69 else 105))) else (if idx < 492 then (if idx < 490 then (if idx < 489 then 63 else 63) else (if idx < 491 then 105 else 69)) else (if idx < 494 then (if idx < 493 then 69 else 69) else 0))))))))

def ret15Quad (idx : Nat) : Nat :=
  (if idx < 8 then (if idx < 4 then (if idx < 2 then (if idx < 1 then 291 else 292) else (if idx < 3 then 293 else 308)) else (if idx < 6 then (if idx < 5 then 309 else 325) else (if idx < 7 then 564 else 565))) else (if idx < 12 then (if idx < 10 then (if idx < 9 then 581 else 837) else (if idx < 11 then 4660 else 4661)) else (if idx < 14 then (if idx < 13 then 4677 else 4933) else 9029)))

def ret15Cert (idx : Nat) : Nat :=
  (if idx < 8 then (if idx < 4 then (if idx < 2 then (if idx < 1 then 352 else 352) else (if idx < 3 then 352 else 352)) else (if idx < 6 then (if idx < 5 then 352 else 352) else (if idx < 7 then 129 else 129))) else (if idx < 12 then (if idx < 10 then (if idx < 9 then 129 else 129) else (if idx < 11 then 153 else 153)) else (if idx < 14 then (if idx < 13 then 153 else 153) else 0)))

/-- Balanced O(log N)-depth range check (`∀ i ∈ [lo, hi), p i = true`), avoiding `maxRecDepth`! -/
def allBelowRangeGo : Nat → Nat → Nat → (Nat → Bool) → Bool
  | 0, _, _, _ => true
  | fuel + 1, lo, hi, p =>
    if hi ≤ lo then true
    else if lo + 1 == hi then p lo
    else
      let mid := (lo + hi) / 2
      allBelowRangeGo fuel lo mid p && allBelowRangeGo fuel mid hi p

def allBelowRange (lo hi : Nat) (p : Nat → Bool) : Bool :=
  allBelowRangeGo 12 lo hi p

/-- Check a contiguous slice `[lo, hi)` of the 495 singleton 4-marginals of `h_uncond`. -/
def checkSingMarg4Slice (lo hi : Nat) : Bool :=
  allBelowRange lo hi fun idx =>
    let q := sing495Quad idx
    let v0 := (q >>> 12) &&& 15
    let v1 := (q >>> 8) &&& 15
    let v2 := (q >>> 4) &&& 15
    let v3 := q &&& 15
    let cp := sing495Cert idx
    let ci := cp / 24
    let pi := cp % 24
    allBelow 15 fun k =>
      hUncondMarg4 (1 <<< v0) (1 <<< v1) (1 <<< v2) (1 <<< v3) (permMask4 pi (k + 1)) == canonProf4At ci k

/-- Check all 15 retrieval-object 4-marginals of `h_uncond`. -/
def checkRet15Marg4 : Bool :=
  allBelow 15 fun idx =>
    let q := ret15Quad idx
    let v0 := (q >>> 12) &&& 15
    let v1 := (q >>> 8) &&& 15
    let v2 := (q >>> 4) &&& 15
    let v3 := q &&& 15
    let cp := ret15Cert idx
    let ci := cp / 24
    let pi := cp % 24
    allBelow 15 fun k =>
      hUncondMarg4 (retObjMask v0) (retObjMask v1) (retObjMask v2) (retObjMask v3) (permMask4 pi (k + 1)) == canonProf4At ci k

/-- Kernel-certified exact check of ALL 495 singleton 4-marginals and ALL 15 retrieval 4-marginals
    (510 four-marginals × 15 nonempty masks = 7,650 exact identities) against `canonProf4At`! -/
def checkAll510Marg4 : Bool :=
  checkSingMarg4Slice 0 100 &&
  checkSingMarg4Slice 100 200 &&
  checkSingMarg4Slice 200 300 &&
  checkSingMarg4Slice 300 400 &&
  checkSingMarg4Slice 400 495 &&
  checkRet15Marg4

theorem checkSingMarg4Slice_0_100 : checkSingMarg4Slice 0 100 = true := by decide
theorem checkSingMarg4Slice_100_200 : checkSingMarg4Slice 100 200 = true := by decide
theorem checkSingMarg4Slice_200_300 : checkSingMarg4Slice 200 300 = true := by decide
theorem checkSingMarg4Slice_300_400 : checkSingMarg4Slice 300 400 = true := by decide
theorem checkSingMarg4Slice_400_495 : checkSingMarg4Slice 400 495 = true := by decide
theorem checkRet15Marg4_ok : checkRet15Marg4 = true := by decide

theorem checkAll510Marg4_ok : checkAll510Marg4 = true := by
  unfold checkAll510Marg4
  rw [checkSingMarg4Slice_0_100, checkSingMarg4Slice_100_200,
      checkSingMarg4Slice_200_300, checkSingMarg4Slice_300_400,
      checkSingMarg4Slice_400_495, checkRet15Marg4_ok]
  rfl

/-- Verify `sing495Quad` enumerates all 495 strictly ordered quadruples `0 ≤ a < b < c < d < 12`
    and `ret15Quad` enumerates all 15 strictly ordered quadruples `0 ≤ a < b < c < d < 6`. -/
def checkQuadEnum495and15 : Bool :=
  let okS := allBelowRange 0 494 fun idx => sing495Quad idx < sing495Quad (idx + 1)
  let okSb := allBelowRange 0 495 fun idx =>
    let q := sing495Quad idx
    let v0 := (q >>> 12) &&& 15; let v1 := (q >>> 8) &&& 15
    let v2 := (q >>> 4) &&& 15; let v3 := q &&& 15
    v0 < v1 && v1 < v2 && v2 < v3 && v3 < 12
  let okR := allBelow 14 fun idx => ret15Quad idx < ret15Quad (idx + 1)
  let okRb := allBelow 15 fun idx =>
    let q := ret15Quad idx
    let v0 := (q >>> 12) &&& 15; let v1 := (q >>> 8) &&& 15
    let v2 := (q >>> 4) &&& 15; let v3 := q &&& 15
    v0 < v1 && v1 < v2 && v2 < v3 && v3 < 6
  okS && okSb && okR && okRb

theorem checkQuadEnum495and15_ok : checkQuadEnum495and15 = true := by decide

/-! ### Exact F_2-Linear Subspace Realizations of ALL 6 Five-Object Retrieval Marginals -/

def hUncondMarg5 (m0 m1 m2 m3 m4 mask : Nat) : Nat :=
  let u0 := if (mask &&& 1) != 0 then m0 else 0
  let u1 := if (mask &&& 2) != 0 then m1 else 0
  let u2 := if (mask &&& 4) != 0 then m2 else 0
  let u3 := if (mask &&& 8) != 0 then m3 else 0
  let u4 := if (mask &&& 16) != 0 then m4 else 0
  hUncond (u0 ||| u1 ||| u2 ||| u3 ||| u4)

def boolSing5Subs (i : Nat) : List (List (List Nat)) :=
  (List.range 5).map (fun k => if k == i then [[1]] else [])

def boolPair5Subs (i j : Nat) : List (List (List Nat)) :=
  (List.range 5).map (fun k => if k == i || k == j then [[1]] else [])

def coreW1Subs : List (List (List Nat)) :=
  [[[0, 0, 1, 0, 1, 0, 1, 0], [1, 0, 0, 0, 0, 1, 1, 1], [0, 1, 0, 1, 0, 0, 0, 1]], [[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0]], [[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]], [[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0]], [[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]]]

def gadgetG1Subs : List (List (List Nat)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0]], [[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], [[0, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0]], [[0, 0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 1]], [[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 1, 1, 1, 0, 1, 1]]]

def gadgetG2Subs : List (List (List Nat)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], [[0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1], [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1]], [[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1], [0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0]], [[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0]]]

def ret5DecompW1 (mask : Nat) : Nat :=
  16 * subspaceRank5 2 coreW1Subs mask
  + 20 * (subspaceRank5 2 (boolPair5Subs 0 1) mask
        + subspaceRank5 2 (boolPair5Subs 0 2) mask
        + subspaceRank5 2 (boolPair5Subs 0 3) mask
        + subspaceRank5 2 (boolPair5Subs 0 4) mask)

def ret5DecompW2 (mask : Nat) : Nat :=
  48 * subspaceRank5 2 (boolSing5Subs 0) mask
  + 20 * (subspaceRank5 2 (boolPair5Subs 0 1) mask
        + subspaceRank5 2 (boolPair5Subs 0 2) mask
        + subspaceRank5 2 (boolPair5Subs 0 3) mask
        + subspaceRank5 2 (boolPair5Subs 0 4) mask)
  + 32 * (subspaceRank5 2 (boolSing5Subs 1) mask
        + subspaceRank5 2 (boolSing5Subs 2) mask
        + subspaceRank5 2 (boolSing5Subs 3) mask
        + subspaceRank5 2 (boolSing5Subs 4) mask)

def ret5DecompW12 (mask : Nat) : Nat :=
  4 * subspaceRank5 2 gadgetG2Subs mask
  + 4 * subspaceRank5 2 gadgetG1Subs mask
  + 20 * (subspaceRank5 2 (boolPair5Subs 0 2) mask
        + subspaceRank5 2 (boolPair5Subs 0 3) mask
        + subspaceRank5 2 (boolPair5Subs 0 4) mask)
  + 12 * (subspaceRank5 2 (boolPair5Subs 1 2) mask
        + subspaceRank5 2 (boolPair5Subs 1 3) mask
        + subspaceRank5 2 (boolPair5Subs 1 4) mask)
  + 32 * subspaceRank5 2 (boolSing5Subs 0) mask
  + 48 * subspaceRank5 2 (boolSing5Subs 1) mask

/-- Kernel-certified check of ALL `C(6,5) = 6` five-object retrieval marginals of `h_uncond`! -/
def checkAll6RetMarg5 : Bool :=
  let okW1 := allBelow 31 fun k =>
    hUncondMarg5 (retObjMask 0) (retObjMask 2) (retObjMask 3) (retObjMask 4) (retObjMask 5) (k + 1)
    == ret5DecompW1 (k + 1)
  let okW2 := allBelow 31 fun k =>
    hUncondMarg5 (retObjMask 1) (retObjMask 2) (retObjMask 3) (retObjMask 4) (retObjMask 5) (k + 1)
    == ret5DecompW2 (k + 1)
  let triples := [(2,3,4), (2,3,5), (2,4,5), (3,4,5)]
  let okW12 := triples.all fun (a, b, c) =>
    allBelow 31 fun k =>
      hUncondMarg5 (retObjMask 0) (retObjMask 1) (retObjMask a) (retObjMask b) (retObjMask c) (k + 1)
      == ret5DecompW12 (k + 1)
  okW1 && okW2 && okW12

theorem checkAll6RetMarg5_ok : checkAll6RetMarg5 = true := by decide

/-! ### Exact Single `F_2^64` Linear-Subspace Realization of ALL 6 Retrieval Objects (`T1j`) -/

/-- Exact 6-variable marginal of `h_uncond` on `{W1, W2, A1, A2, A3, A4}` (`mask ∈ 1..63`). -/
def hUncondRet6 (mask : Nat) : Nat :=
  let u0 := if (mask &&& 1) != 0 then retObjMask 0 else 0
  let u1 := if (mask &&& 2) != 0 then retObjMask 1 else 0
  let u2 := if (mask &&& 4) != 0 then retObjMask 2 else 0
  let u3 := if (mask &&& 8) != 0 then retObjMask 3 else 0
  let u4 := if (mask &&& 16) != 0 then retObjMask 4 else 0
  let u5 := if (mask &&& 32) != 0 then retObjMask 5 else 0
  hUncond (u0 ||| u1 ||| u2 ||| u3 ||| u4 ||| u5)

/-- Evaluate a 6-variable integer linear functional `c` (on masks 1..63) on a rank function `r`. -/
def evalFunc6 (c : Nat → Int) (r : Nat → Nat) : Int :=
  evalFuncGo c r 63

/-- Toggle bit `b` in a strictly increasing `List Nat` (exact `F_2` addition of `e_b`, pure structural recursion). -/
def toggleBit (b : Nat) : List Nat → List Nat
  | [] => [b]
  | x :: xs =>
    if b < x then b :: x :: xs
    else if b == x then xs
    else x :: toggleBit b xs

/-- Normalize any list of coordinate indices `< d` into a canonical strictly increasing `F_2^d` support. -/
def toSparseF2Go (d : Nat) : List Nat → List Nat → List Nat
  | [], acc => acc
  | b :: bs, acc => toSparseF2Go d bs (if b < d then toggleBit b acc else acc)

def toSparseF2 (d : Nat) (bits : List Nat) : List Nat :=
  toSparseF2Go d bits []

/-- Exact `F_2` vector XOR on strictly increasing `List Nat` supports (100% structural recursion!). -/
def xorSparse (a : List Nat) : List Nat → List Nat
  | [] => a
  | x :: xs => xorSparse (toggleBit x a) xs

/-- Transparent bucket lookup (zero external `List.lookup` module opacity!). -/
def bucketLookup (key : Nat) : List (Nat × List Nat) → Option (List Nat)
  | [] => none
  | (k, row) :: rest => if k == key then some row else bucketLookup key rest

/-- 6-level binary radix trie (`0..63` in exact depth 6, bucketed mod 64 for arbitrary `d : Nat`). -/
inductive PivotTrie where
  | empty
  | leaf (bucket : List (Nat × List Nat))
  | node (l r : PivotTrie)

def trieLookup : Nat → Nat → Nat → PivotTrie → Option (List Nat)
  | _, _, _, PivotTrie.empty => none
  | _, key, _, PivotTrie.leaf b => bucketLookup key b
  | 0, _, _, PivotTrie.node _ _ => none
  | d + 1, key, bits, PivotTrie.node l r =>
    if bits % 2 == 0 then trieLookup d key (bits / 2) l else trieLookup d key (bits / 2) r

def trieInsert : Nat → Nat → Nat → List Nat → PivotTrie → PivotTrie
  | 0, key, _, row, PivotTrie.empty => PivotTrie.leaf [(key, row)]
  | 0, key, _, row, PivotTrie.leaf b => PivotTrie.leaf ((key, row) :: b)
  | 0, _, _, _, PivotTrie.node l r => PivotTrie.node l r
  | d + 1, key, bits, row, PivotTrie.empty =>
    if bits % 2 == 0 then
      PivotTrie.node (trieInsert d key (bits / 2) row PivotTrie.empty) PivotTrie.empty
    else
      PivotTrie.node PivotTrie.empty (trieInsert d key (bits / 2) row PivotTrie.empty)
  | _ + 1, key, _, row, PivotTrie.leaf b => PivotTrie.leaf ((key, row) :: b)
  | d + 1, key, bits, row, PivotTrie.node l r =>
    if bits % 2 == 0 then
      PivotTrie.node (trieInsert d key (bits / 2) row l) r
    else
      PivotTrie.node l (trieInsert d key (bits / 2) row r)

def reduceSparse : Nat → PivotTrie → List Nat → List Nat
  | 0, _, v => v
  | _, _, [] => []
  | fuel + 1, t, p :: rest =>
    match trieLookup 6 p p t with
    | none => p :: rest
    | some brow => reduceSparse fuel t (xorSparse (p :: rest) brow)

def gf2RankSparseGo (d : Nat) : List (List Nat) → PivotTrie → Nat → Nat
  | [], _, rk => rk
  | row :: rest, t, rk =>
    let v := toSparseF2 d row
    match reduceSparse d t v with
    | [] => gf2RankSparseGo d rest t rk
    | p :: pt => gf2RankSparseGo d rest (trieInsert 6 p p (p :: pt) t) (rk + 1)

/-- Exact `F_2^d` Gaussian elimination rank on sparse coordinate-support rows (100% structural recursion,
    zero `Nat.bitwise`, zero `WellFounded.fix`, blazingly fast across ALL 6 proof kernels!). -/
def gf2RankSparse (d : Nat) (rows : List (List Nat)) : Nat :=
  gf2RankSparseGo d rows PivotTrie.empty 0

/-- Transparent list indexing helper (zero `List.getD` / `List.range` module opacity). -/
def getSub6 : List (List (List Nat)) → Nat → List (List Nat)
  | [], _ => []
  | x :: _, 0 => x
  | _ :: xs, n + 1 => getSub6 xs n

/-- Exact 6-subspace rank over `F_2^d` for any `mask ∈ 1..63` (each row given by its set-bit indices). -/
def subspaceRank6F2 (d : Nat) (subs : List (List (List Nat))) (mask : Nat) : Nat :=
  let s0 := if (mask % 2) == 1 then getSub6 subs 0 else []
  let s1 := if ((mask / 2) % 2) == 1 then getSub6 subs 1 else []
  let s2 := if ((mask / 4) % 2) == 1 then getSub6 subs 2 else []
  let s3 := if ((mask / 8) % 2) == 1 then getSub6 subs 3 else []
  let s4 := if ((mask / 16) % 2) == 1 then getSub6 subs 4 else []
  let s5 := if ((mask / 32) % 2) == 1 then getSub6 subs 5 else []
  gf2RankSparse d (s0 ++ s1 ++ s2 ++ s3 ++ s4 ++ s5)

/-- Helper building `[base, base+1, ..., base+len-1]` as singleton unit-vector rows `[b]` (100% transparent). -/
def unitRows (base : Nat) : Nat → List (List Nat)
  | 0 => []
  | n + 1 => [base] :: unitRows (base + 1) n

/-- The 3 sparse 3-bit `Z_4`-cyclic generator rows in `F_2^20` (total weight 9!):
    `[8, 17, 19]`, `[11, 12, 18]`, `[5, 11, 18]` rotated by `+5i mod 20` for server `i ∈ {0..3}`. -/
def ret6CyclicBaseBits : List (List Nat) :=
  [[8, 17, 19], [11, 12, 18], [5, 11, 18]]

/-- Server `i`'s 3 paired interference vectors shifted into `W_2` coordinates `32..51` of `F_2^64`. -/
def ret6ServerPairedRows (i : Nat) : List (List Nat) :=
  [ [20 + 3 * i + 0, 32 + (8 + 5 * i) % 20, 32 + (17 + 5 * i) % 20, 32 + (19 + 5 * i) % 20],
    [20 + 3 * i + 1, 32 + (11 + 5 * i) % 20, 32 + (12 + 5 * i) % 20, 32 + (18 + 5 * i) % 20],
    [20 + 3 * i + 2, 32 + (5 + 5 * i) % 20, 32 + (11 + 5 * i) % 20, 32 + (18 + 5 * i) % 20] ]

/-- Server `i`'s 13-dimensional subspace `A_i ⊂ F_2^64`:
    5 pure `W_1` basis vectors (`P_i`), 5 pure `W_2` basis vectors (`Q_i`), and 3 paired vectors. -/
def ret6ServerSub (i : Nat) : List (List Nat) :=
  unitRows (5 * i) 5 ++ unitRows (32 + 5 * i) 5 ++ ret6ServerPairedRows i

/-- The SINGLE explicit `F_2^64` 6-subspace arrangement `(W1, W2, A0, A1, A2, A3)` realizing
    ALL 64 subset entropies of `h_uncond` on `{W1, W2, A1, A2, A3, A4}` at exact scale factor 4! -/
def ret6F2Arrangement : List (List (List Nat)) :=
  [ unitRows 0 32,
    unitRows 32 32,
    ret6ServerSub 0,
    ret6ServerSub 1,
    ret6ServerSub 2,
    ret6ServerSub 3 ]

/-- Slice helper checking `hUncondRet6 m == 4 * subspaceRank6F2 64 ret6F2Arrangement m` on `[lo, hi)`. -/
def checkRet6F2Slice (lo hi : Nat) : Bool :=
  allBelow (hi - lo) fun t =>
    let m := lo + t
    hUncondRet6 m == 4 * subspaceRank6F2 64 ret6F2Arrangement m

private theorem allBelow_ok (n : Nat) (p : Nat → Bool) (h : allBelow n p = true) :
    ∀ k, k < n → p k = true := by
  induction n with
  | zero => intro _ hk; omega
  | succ m ih =>
    simp only [allBelow, Bool.and_eq_true] at h
    intro k hk
    cases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hk) with
    | inl heq => subst heq; exact h.2
    | inr hlt => exact ih h.1 k hlt

/-- Balanced sliced kernel verification of ALL 63 non-empty subsets of `(W1, W2, A0, A1, A2, A3)`
    directly in `F_2^64` (`0` mismatches, zero `native_decide`, blazingly fast across all 6 kernels!). -/
theorem checkRet6F2Slice_1_16 : checkRet6F2Slice 1 16 = true := by decide
theorem checkRet6F2Slice_16_32 : checkRet6F2Slice 16 32 = true := by decide
theorem checkRet6F2Slice_32_48 : checkRet6F2Slice 32 48 = true := by decide
theorem checkRet6F2Slice_48_64 : checkRet6F2Slice 48 64 = true := by decide

/-- Exact `F_2^64` realization theorem for EVERY mask `1 ≤ m ≤ 63`:
    `hUncondRet6 m = 4 * subspaceRank6F2 64 ret6F2Arrangement m`. -/
theorem h_uncond_ret6_eq_4_times_f2_64 :
    ∀ m : Nat, 1 ≤ m → m ≤ 63 →
      hUncondRet6 m = 4 * subspaceRank6F2 64 ret6F2Arrangement m := by
  intro m hm1 hm63
  by_cases h1 : m < 16
  · have h := allBelow_ok 15 _ checkRet6F2Slice_1_16 (m - 1) (by omega)
    have hidx : 1 + (m - 1) = m := by omega
    rw [hidx] at h; exact beq_iff_eq.mp h
  · by_cases h2 : m < 32
    · have h := allBelow_ok 16 _ checkRet6F2Slice_16_32 (m - 16) (by omega)
      have hidx : 16 + (m - 16) = m := by omega
      rw [hidx] at h; exact beq_iff_eq.mp h
    · by_cases h3 : m < 48
      · have h := allBelow_ok 16 _ checkRet6F2Slice_32_48 (m - 32) (by omega)
        have hidx : 32 + (m - 32) = m := by omega
        rw [hidx] at h; exact beq_iff_eq.mp h
      · have h := allBelow_ok 16 _ checkRet6F2Slice_48_64 (m - 48) (by omega)
        have hidx : 48 + (m - 48) = m := by omega
        rw [hidx] at h; exact beq_iff_eq.mp h

end
end TriadFrontier.PIRLinearCerts
