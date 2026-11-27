// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Alexander S. Donahue
// Portable Forward-Mode Dual-Number AD Evaluator for Eshkol v1.3.6 S-expression modules (`eshkol/*.esk`).

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const MAX_PARSE_DEPTH = 256;
const MAX_EVAL_DEPTH = 256;
const MAX_EVAL_STEPS = 100000;

class Dual {
  constructor(val, dot = 0.0) {
    if (!Number.isFinite(val) || !Number.isFinite(dot)) {
      throw new RangeError(`Non-finite Dual value: (${val}, ${dot})`);
    }
    this.val = val;
    this.dot = dot;
  }
}

const isDual = (x) => x instanceof Dual;
const valOf = (x) => (isDual(x) ? x.val : x);
const dotOf = (x) => (isDual(x) ? x.dot : 0.0);
const toDual = (x) => (isDual(x) ? x : new Dual(x, 0.0));

function assertFiniteNum(x, op) {
  const v = valOf(x);
  if (typeof v !== 'number' || !Number.isFinite(v)) {
    throw new RangeError(`Non-finite numeric argument in ${op}: ${v}`);
  }
  return v;
}

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
      let closed = false;
      while (i < src.length) {
        if (src[i] === '\\' && i + 1 < src.length) {
          s += src[i] + src[i + 1];
          i += 2;
          continue;
        }
        if (src[i] === '"') {
          s += '"';
          i++;
          closed = true;
          break;
        }
        s += src[i++];
      }
      if (!closed) {
        throw new SyntaxError('Unterminated string literal in Eshkol source');
      }
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
  function readExpr(depth) {
    if (depth > MAX_PARSE_DEPTH) {
      throw new RangeError(`Maximum parse depth (${MAX_PARSE_DEPTH}) exceeded`);
    }
    if (pos >= tokens.length) {
      throw new SyntaxError('Unexpected end of token stream');
    }
    const tok = tokens[pos++];
    if (tok === ')') {
      throw new SyntaxError('Unexpected closing parenthesis ")"');
    }
    if (tok === '(') {
      const list = [];
      while (pos < tokens.length && tokens[pos] !== ')') {
        list.push(readExpr(depth + 1));
      }
      if (pos >= tokens.length || tokens[pos] !== ')') {
        throw new SyntaxError('Unterminated S-expression (missing closing ")")');
      }
      pos++;
      return list;
    }
    if (tok.startsWith('"')) return { str: JSON.parse(tok) };
    if (/^[+-]?(\d+\.?\d*|\.\d+)([eE][+-]?\d+)?$/.test(tok)) {
      const num = Number(tok);
      if (!Number.isFinite(num)) throw new RangeError(`Non-finite numeric literal: ${tok}`);
      return num;
    }
    return { sym: tok };
  }
  const forms = [];
  while (pos < tokens.length) forms.push(readExpr(0));
  return forms;
}

const dAdd = (a, b) => {
  assertFiniteNum(a, '+');
  assertFiniteNum(b, '+');
  return (isDual(a) || isDual(b)) ? new Dual(valOf(a) + valOf(b), dotOf(a) + dotOf(b)) : a + b;
};
const dSub = (a, b) => {
  assertFiniteNum(a, '-');
  assertFiniteNum(b, '-');
  return (isDual(a) || isDual(b)) ? new Dual(valOf(a) - valOf(b), dotOf(a) - dotOf(b)) : a - b;
};
const dMul = (a, b) => {
  assertFiniteNum(a, '*');
  assertFiniteNum(b, '*');
  if (isDual(a) || isDual(b)) {
    const da = toDual(a), db = toDual(b);
    return new Dual(da.val * db.val, da.dot * db.val + da.val * db.dot);
  }
  return a * b;
};
const dDiv = (a, b) => {
  assertFiniteNum(a, '/');
  const bv = assertFiniteNum(b, '/');
  if (bv === 0) throw new RangeError('Division by zero in Eshkol AD evaluator');
  if (isDual(a) || isDual(b)) {
    const da = toDual(a), db = toDual(b);
    return new Dual(da.val / db.val, (da.dot * db.val - da.val * db.dot) / (db.val * db.val));
  }
  return a / b;
};

export function evaluateEshkol(src) {
  if (typeof src !== 'string') {
    throw new TypeError('evaluateEshkol expects a string source');
  }
  const forms = parse(tokenize(src));
  const out = [];
  let line = '';
  let steps = 0;

  const globalEnv = new Map([
    ['+', (...args) => args.reduce(dAdd, 0)],
    ['-', (...args) => {
      if (args.length === 0) throw new RangeError('Operator "-" requires at least 1 argument');
      return args.length === 1 ? dSub(0, args[0]) : args.slice(1).reduce(dSub, args[0]);
    }],
    ['*', (...args) => args.reduce(dMul, 1)],
    ['/', (...args) => {
      if (args.length === 0) throw new RangeError('Operator "/" requires at least 1 argument');
      return args.length === 1 ? dDiv(1, args[0]) : args.slice(1).reduce(dDiv, args[0]);
    }],
    ['exp', (x) => {
      const v = assertFiniteNum(x, 'exp');
      const evv = Math.exp(v);
      if (!Number.isFinite(evv)) throw new RangeError(`exp overflow at ${v}`);
      return isDual(x) ? new Dual(evv, evv * x.dot) : evv;
    }],
    ['log', (x) => {
      const v = assertFiniteNum(x, 'log');
      if (v <= 0) throw new RangeError(`log domain error at ${v}`);
      return isDual(x) ? new Dual(Math.log(v), x.dot / v) : Math.log(v);
    }],
    ['sqrt', (x) => {
      const v = assertFiniteNum(x, 'sqrt');
      if (v < 0) throw new RangeError(`sqrt domain error at ${v}`);
      if (isDual(x)) {
        if (v === 0) throw new RangeError('sqrt derivative singular at 0');
        return new Dual(Math.sqrt(v), x.dot / (2 * Math.sqrt(v)));
      }
      return Math.sqrt(v);
    }],
    ['derivative', (fn, x0) => {
      if (typeof fn !== 'function') throw new TypeError('derivative expects a callable function');
      const v = assertFiniteNum(x0, 'derivative');
      return dotOf(fn(new Dual(v, 1.0)));
    }],
    ['display', (x) => { line += typeof x === 'string' ? x : String(valOf(x)); return null; }],
    ['newline', () => { out.push(line); line = ''; return null; }],
  ]);

  function lookup(name, env) {
    if (env.has(name)) return env.get(name);
    throw new Error(`Unbound symbol: ${name}`);
  }

  function ev(expr, env, depth = 0) {
    steps += 1;
    if (steps > MAX_EVAL_STEPS) {
      throw new RangeError(`Maximum evaluation step budget (${MAX_EVAL_STEPS}) exceeded`);
    }
    if (depth > MAX_EVAL_DEPTH) {
      throw new RangeError(`Maximum evaluation recursion depth (${MAX_EVAL_DEPTH}) exceeded`);
    }
    if (typeof expr === 'number') return expr;
    if (expr && typeof expr === 'object' && 'str' in expr) return expr.str;
    if (expr && typeof expr === 'object' && 'sym' in expr) return lookup(expr.sym, env);
    if (!Array.isArray(expr) || expr.length === 0) {
      throw new SyntaxError('Empty or invalid S-expression application');
    }
    const head = expr[0]?.sym;
    if (head === 'define') {
      if (expr.length < 3) throw new SyntaxError('Malformed define form');
      if (Array.isArray(expr[1])) {
        if (expr[1].length === 0 || !expr[1][0]?.sym) throw new SyntaxError('Malformed define signature');
        const fname = expr[1][0].sym;
        const params = expr[1].slice(1).map((p) => {
          if (!p?.sym) throw new SyntaxError('Malformed parameter name in define');
          return p.sym;
        });
        const body = expr.slice(2);
        const fn = (...args) => {
          if (args.length !== params.length) {
            throw new RangeError(`Function ${fname} expected ${params.length} args, got ${args.length}`);
          }
          const child = new Map(env);
          params.forEach((p, i) => child.set(p, args[i]));
          let val = null;
          for (const b of body) val = ev(b, child, depth + 1);
          return val;
        };
        env.set(fname, fn);
        return fn;
      }
      if (!expr[1]?.sym) throw new SyntaxError('Malformed variable name in define');
      const val = ev(expr[2], env, depth + 1);
      env.set(expr[1].sym, val);
      return val;
    }
    if (head === 'let') {
      if (expr.length < 3 || !Array.isArray(expr[1])) throw new SyntaxError('Malformed let form');
      const bindings = expr[1];
      const child = new Map(env);
      for (const b of bindings) {
        if (!Array.isArray(b) || b.length !== 2 || !b[0]?.sym) throw new SyntaxError('Malformed let binding');
        child.set(b[0].sym, ev(b[1], env, depth + 1));
      }
      let val = null;
      for (const bodyExpr of expr.slice(2)) val = ev(bodyExpr, child, depth + 1);
      return val;
    }
    const fn = ev(expr[0], env, depth + 1);
    if (typeof fn !== 'function') {
      throw new TypeError(`Attempted to call non-function: ${String(expr[0]?.sym ?? expr[0])}`);
    }
    const args = expr.slice(1).map((a) => ev(a, env, depth + 1));
    return fn(...args);
  }

  for (const f of forms) ev(f, globalEnv, 0);
  if (line) out.push(line);
  return out;
}

function assertFiniteClose(name, actual, expected, tol) {
  if (typeof actual !== 'number' || !Number.isFinite(actual)) {
    throw new Error(`${name}: expected finite number, got ${actual}`);
  }
  if (!(Math.abs(actual - expected) <= tol)) {
    throw new Error(`${name}: |${actual} - ${expected}| > ${tol}`);
  }
}

function assertFiniteAbsGe(name, actual, threshold) {
  if (typeof actual !== 'number' || !Number.isFinite(actual)) {
    throw new Error(`${name}: expected finite number, got ${actual}`);
  }
  if (!(Math.abs(actual) >= threshold)) {
    throw new Error(`${name}: |${actual}| < ${threshold}`);
  }
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
  assertFiniteClose('CBD2_DR2_DSIGMA', kv.CBD2_DR2_DSIGMA, 0.0, 1e-3);
  assertFiniteClose('CBD3_DR2_DSIGMA', kv.CBD3_DR2_DSIGMA, 0.0, 1e-3);
  assertFiniteClose('DYADIC256_DR2_DSIGMA', kv.DYADIC256_DR2_DSIGMA, 0.0, 1e-3);
  assertFiniteClose('DYADIC256_R2_OPT', kv.DYADIC256_R2_OPT, 1.000723969787, 1e-9);
  assertFiniteClose('DYADIC512_DR2_DSIGMA', kv.DYADIC512_DR2_DSIGMA, 0.0, 1e-3);
  assertFiniteClose('DYADIC512_R2_OPT', kv.DYADIC512_R2_OPT, 1.000400858061, 1e-9);
  assertFiniteClose('DYADIC1024A_DR2_DSIGMA', kv.DYADIC1024A_DR2_DSIGMA, 0.0, 1e-3);
  assertFiniteClose('DYADIC1024A_R2_OPT', kv.DYADIC1024A_R2_OPT, 1.000510798009, 1e-9);
  assertFiniteClose('DYADIC1024B_DR2_DSIGMA', kv.DYADIC1024B_DR2_DSIGMA, 0.0, 1e-3);
  assertFiniteClose('DYADIC1024B_R2_OPT', kv.DYADIC1024B_R2_OPT, 1.000756813797, 1e-8);
  assertFiniteClose('DYADIC16384A_DR2_DSIGMA', kv.DYADIC16384A_DR2_DSIGMA, 0.0, 1e-3);
  assertFiniteClose('DYADIC16384A_R2_OPT', kv.DYADIC16384A_R2_OPT, 1.000390198995, 1e-9);
  assertFiniteClose('DYADIC16384B_DR2_DSIGMA', kv.DYADIC16384B_DR2_DSIGMA, 0.0, 1e-3);
  assertFiniteClose('DYADIC16384B_R2_OPT', kv.DYADIC16384B_R2_OPT, 1.000015905984, 1e-8);
  assertFiniteClose('KOSZUL_RATE_E6', kv.KOSZUL_RATE_E6, 10 / 17, 1e-12);
  assertFiniteClose('QGTL_OMEGA_E0_0', kv.QGTL_OMEGA_E0_0, 0.0, 1e-15);
  assertFiniteAbsGe('QGTL_OMEGA_E0_035', kv.QGTL_OMEGA_E0_035, 1e-3);
  console.error('All 3 Eshkol v1.3.6 dual-number AD modules PASSED.');
}
