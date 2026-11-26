// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Alexander S. Donahue
// Portable Forward-Mode Dual-Number AD Evaluator for Eshkol v1.3.6 S-expression modules (`eshkol/*.esk`).

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

class Dual {
  constructor(val, dot = 0.0) {
    this.val = val;
    this.dot = dot;
  }
}

const isDual = (x) => x instanceof Dual;
const valOf = (x) => (isDual(x) ? x.val : x);
const dotOf = (x) => (isDual(x) ? x.dot : 0.0);
const toDual = (x) => (isDual(x) ? x : new Dual(x, 0.0));

function tokenize(src) {
  const tokens = [];
  let i = 0;
  while (i < src.length) {
    const ch = src[i];
    if (ch === ';') {
      while (i < src.length && src[i] !== '\n') i++;
    } else if (/\s/.test(ch)) {
      i++;
    } else if (ch === '(' || ch === ')') {
      tokens.push(ch);
      i++;
    } else if (ch === '"') {
      let s = '"';
      i++;
      while (i < src.length && src[i] !== '"') s += src[i++];
      s += '"';
      i++;
      tokens.push(s);
    } else {
      let atom = '';
      while (i < src.length && !/[\s()";]/.test(src[i])) atom += src[i++];
      tokens.push(atom);
    }
  }
  return tokens;
}

function parse(tokens) {
  let pos = 0;
  function readExpr() {
    const tok = tokens[pos++];
    if (tok === '(') {
      const list = [];
      while (pos < tokens.length && tokens[pos] !== ')') list.push(readExpr());
      pos++;
      return list;
    }
    if (tok.startsWith('"')) return { str: JSON.parse(tok) };
    if (/^[+-]?(\d+\.?\d*|\.\d+)([eE][+-]?\d+)?$/.test(tok)) return Number(tok);
    return { sym: tok };
  }
  const forms = [];
  while (pos < tokens.length) forms.push(readExpr());
  return forms;
}

const dAdd = (a, b) => (isDual(a) || isDual(b)) ? new Dual(valOf(a) + valOf(b), dotOf(a) + dotOf(b)) : a + b;
const dSub = (a, b) => (isDual(a) || isDual(b)) ? new Dual(valOf(a) - valOf(b), dotOf(a) - dotOf(b)) : a - b;
const dMul = (a, b) => {
  if (isDual(a) || isDual(b)) {
    const da = toDual(a), db = toDual(b);
    return new Dual(da.val * db.val, da.dot * db.val + da.val * db.dot);
  }
  return a * b;
};
const dDiv = (a, b) => {
  if (isDual(a) || isDual(b)) {
    const da = toDual(a), db = toDual(b);
    return new Dual(da.val / db.val, (da.dot * db.val - da.val * db.dot) / (db.val * db.val));
  }
  return a / b;
};

export function evaluateEshkol(src) {
  const forms = parse(tokenize(src));
  const out = [];
  let line = '';
  const globalEnv = new Map([
    ['+', (...args) => args.reduce(dAdd, 0)],
    ['-', (...args) => (args.length === 1 ? dSub(0, args[0]) : args.slice(1).reduce(dSub, args[0]))],
    ['*', (...args) => args.reduce(dMul, 1)],
    ['/', (...args) => (args.length === 1 ? dDiv(1, args[0]) : args.slice(1).reduce(dDiv, args[0]))],
    ['exp', (x) => (isDual(x) ? new Dual(Math.exp(x.val), Math.exp(x.val) * x.dot) : Math.exp(x))],
    ['log', (x) => (isDual(x) ? new Dual(Math.log(x.val), x.dot / x.val) : Math.log(x))],
    ['sqrt', (x) => (isDual(x) ? new Dual(Math.sqrt(x.val), x.dot / (2 * Math.sqrt(x.val))) : Math.sqrt(x))],
    ['derivative', (fn, x0) => dotOf(fn(new Dual(valOf(x0), 1.0)))],
    ['display', (x) => { line += typeof x === 'string' ? x : String(valOf(x)); return null; }],
    ['newline', () => { out.push(line); line = ''; return null; }],
  ]);

  function lookup(name, env) {
    if (env.has(name)) return env.get(name);
    throw new Error(`Unbound symbol: ${name}`);
  }

  function ev(expr, env) {
    if (typeof expr === 'number') return expr;
    if (expr && typeof expr === 'object' && 'str' in expr) return expr.str;
    if (expr && typeof expr === 'object' && 'sym' in expr) return lookup(expr.sym, env);
    if (!Array.isArray(expr) || expr.length === 0) return null;
    const head = expr[0]?.sym;
    if (head === 'define') {
      if (Array.isArray(expr[1])) {
        const fname = expr[1][0].sym;
        const params = expr[1].slice(1).map((p) => p.sym);
        const body = expr.slice(2);
        const fn = (...args) => {
          const child = new Map(env);
          params.forEach((p, i) => child.set(p, args[i]));
          let val = null;
          for (const b of body) val = ev(b, child);
          return val;
        };
        env.set(fname, fn);
        return fn;
      }
      const val = ev(expr[2], env);
      env.set(expr[1].sym, val);
      return val;
    }
    if (head === 'let') {
      const bindings = expr[1];
      const child = new Map(env);
      for (const b of bindings) child.set(b[0].sym, ev(b[1], env));
      let val = null;
      for (const bodyExpr of expr.slice(2)) val = ev(bodyExpr, child);
      return val;
    }
    const fn = ev(expr[0], env);
    const args = expr.slice(1).map((a) => ev(a, env));
    return fn(...args);
  }

  for (const f of forms) ev(f, globalEnv);
  if (line) out.push(line);
  return out;
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const dir = path.dirname(fileURLToPath(import.meta.url));
  const files = ['renyi_cbd_ad.esk', 'koszul_pir_ad.esk', 'qgtl_lwe_berry_ad.esk'];
  const kv = {};
  for (const fn of files) {
    const lines = evaluateEshkol(fs.readFileSync(path.join(dir, fn), 'utf8'));
    for (const ln of lines) {
      const idx = ln.indexOf('=');
      if (idx > 0) kv[ln.slice(0, idx)] = Number(ln.slice(idx + 1));
    }
  }
  console.log(JSON.stringify(kv, null, 2));
  if (Math.abs(kv.CBD2_DR2_DSIGMA) > 1e-3) throw new Error('CBD2 stationarity check failed');
  if (Math.abs(kv.CBD3_DR2_DSIGMA) > 1e-3) throw new Error('CBD3 stationarity check failed');
  if (Math.abs(kv.DYADIC256_DR2_DSIGMA) > 1e-3) throw new Error('Dyadic-256 stationarity check failed');
  if (Math.abs(kv.DYADIC256_R2_OPT - 1.000723969787) > 1e-9) throw new Error('Dyadic-256 R2 optimum mismatch');
  if (Math.abs(kv.DYADIC512_DR2_DSIGMA) > 1e-3) throw new Error('Dyadic-512 stationarity check failed');
  if (Math.abs(kv.DYADIC512_R2_OPT - 1.000400858061) > 1e-9) throw new Error('Dyadic-512 R2 optimum mismatch');
  if (Math.abs(kv.DYADIC1024A_DR2_DSIGMA) > 1e-3) throw new Error('Dyadic-1024-A stationarity check failed');
  if (Math.abs(kv.DYADIC1024A_R2_OPT - 1.000510798009) > 1e-9) throw new Error('Dyadic-1024-A R2 optimum mismatch');
  if (Math.abs(kv.DYADIC1024B_DR2_DSIGMA) > 1e-3) throw new Error('Dyadic-1024-B stationarity check failed');
  if (Math.abs(kv.DYADIC1024B_R2_OPT - 1.000756813797) > 1e-8) throw new Error('Dyadic-1024-B R2 optimum mismatch');
  if (Math.abs(kv.KOSZUL_RATE_E6 - 10 / 17) > 1e-12) throw new Error('Koszul E=6 rate mismatch');
  if (Math.abs(kv.QGTL_OMEGA_E0_0) > 1e-15) throw new Error('QGTL symmetry vanishing failed');
  if (Math.abs(kv.QGTL_OMEGA_E0_035) < 1e-3) throw new Error('QGTL bias witness failed');
  console.error('All 3 Eshkol v1.3.6 dual-number AD modules PASSED.');
}
