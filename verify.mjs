#!/usr/bin/env node
/**
 * Independent checker for 証素 certificates.
 * Usage: node verify.mjs certificate.json
 *
 * It does not search for factors. A passing certificate is a proof.
 */
import { readFile } from "node:fs/promises";

const MR_ROWS = [
  { bound: 2047n, witnesses: [2n] },
  { bound: 1373653n, witnesses: [2n, 3n] },
  { bound: 25326001n, witnesses: [2n, 3n, 5n] },
  { bound: 3215031751n, witnesses: [2n, 3n, 5n, 7n] },
  { bound: 2152302898747n, witnesses: [2n, 3n, 5n, 7n, 11n] },
  { bound: 3474749660383n, witnesses: [2n, 3n, 5n, 7n, 11n, 13n] },
  { bound: 341550071728321n, witnesses: [2n, 3n, 5n, 7n, 11n, 13n, 17n] },
  { bound: 3825123056546413051n, witnesses: [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n] },
  {
    bound: 318665857834031151167461n,
    witnesses: [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n],
  },
  {
    bound: 3317044064679887385961981n,
    witnesses: [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n, 41n],
  },
];

function gcd(a, b) {
  let x = a < 0n ? -a : a;
  let y = b < 0n ? -b : b;
  while (y !== 0n) {
    const t = x % y;
    x = y;
    y = t;
  }
  return x;
}

function modPow(base, exp, mod) {
  let b = ((base % mod) + mod) % mod;
  let e = exp;
  let r = 1n;
  while (e > 0n) {
    if (e & 1n) r = (r * b) % mod;
    e >>= 1n;
    b = (b * b) % mod;
  }
  return r;
}

function isqrt(n) {
  if (n < 2n) return n;
  let x = 1n << BigInt((n.toString(2).length + 1) >> 1);
  for (;;) {
    const y = (x + n / x) >> 1n;
    if (y >= x) return x;
    x = y;
  }
}

function isSquare(n) {
  if (n < 0n) return false;
  const r = isqrt(n);
  return r * r === n;
}

function num(text, label) {
  if (typeof text !== "string" || !/^[0-9]+$/.test(text)) {
    throw new Error(`${label} is not a decimal integer`);
  }
  return BigInt(text);
}

function mrPasses(n, a) {
  let d = n - 1n;
  let s = 0n;
  while ((d & 1n) === 0n) {
    d >>= 1n;
    s += 1n;
  }
  let x = modPow(a, d, n);
  if (x === 1n || x === n - 1n) return true;
  for (let r = 1n; r < s; r++) {
    x = (x * x) % n;
    if (x === n - 1n) return true;
  }
  return false;
}

function verify(cert, depth = 0) {
  if (!cert || cert.v !== 1) return fail("unsupported certificate");
  if (depth > 64) return fail("certificate too deep");
  switch (cert.kind) {
    case "two":
      return ok("prime", 2n);
    case "factor":
      return verifyFactor(cert);
    case "fermat":
      return verifyFermat(cert);
    case "mr-composite":
      return verifyMrComposite(cert);
    case "mr":
      return verifyMr(cert);
    case "ll":
    case "ll-composite":
      return verifyLl(cert, depth);
    case "pocklington":
      return verifyPocklington(cert, depth);
    default:
      return fail(`unknown kind ${cert.kind}`);
  }
}

function ok(status, n) {
  return { ok: true, status, n };
}
function fail(reason) {
  return { ok: false, reason };
}

function verifyFactor(cert) {
  const n = num(cert.n, "n");
  const f = num(cert.factor, "factor");
  if (f <= 1n || f >= n || n % f !== 0n) return fail("factor does not divide n");
  return ok("composite", n);
}

function verifyFermat(cert) {
  const n = num(cert.n, "n");
  const a = num(cert.a, "a");
  if (a <= 1n || a >= n || gcd(a, n) !== 1n) return fail("bad Fermat base");
  if (modPow(a, n - 1n, n) === 1n) return fail("Fermat condition does not prove composite");
  return ok("composite", n);
}

function verifyMrComposite(cert) {
  const n = num(cert.n, "n");
  const a = num(cert.a, "a");
  if (n % 2n === 0n) return verifyFactor({ n: cert.n, factor: "2" });
  if (a <= 1n || a >= n || gcd(a, n) !== 1n) return fail("bad MR base");
  if (mrPasses(n, a)) return fail("base does not prove composite");
  return ok("composite", n);
}

function verifyMr(cert) {
  const n = num(cert.n, "n");
  const bound = num(cert.bound, "bound");
  const row = MR_ROWS.find((item) => item.bound === bound);
  if (!row) return fail("unknown deterministic bound");
  if (n >= bound || n % 2n === 0n) return fail("n is outside the bound");
  const got = (cert.witnesses ?? []).map((w) => num(w, "witness"));
  if (got.length !== row.witnesses.length || got.some((w, i) => w !== row.witnesses[i])) {
    return fail("witness row does not match the theorem");
  }
  for (const a of row.witnesses) {
    if (a >= n) continue;
    if (!mrPasses(n, a)) return fail(`fails at base ${a}`);
  }
  return ok("prime", n);
}

function lucasLehmerResidue(p) {
  const m = (1n << p) - 1n;
  let s = 4n;
  for (let i = 0n; i < p - 2n; i++) {
    s = (s * s - 2n) % m;
    if (s < 0n) s += m;
  }
  return s;
}

function verifyLl(cert, depth) {
  const p = num(cert.p, "p");
  const pVerified = verify(cert.pCert, depth + 1);
  if (!pVerified.ok || pVerified.status !== "prime" || pVerified.n !== p) {
    return fail("exponent certificate failed");
  }
  if (p > 20000n) return fail("Lucas-Lehmer limit");
  const n = (1n << p) - 1n;
  const residue = p === 2n ? 0n : lucasLehmerResidue(p);
  if (cert.kind === "ll") {
    return residue === 0n ? ok("prime", n) : fail("Lucas-Lehmer residue is not 0");
  }
  return residue === 0n ? fail("residue is 0") : ok("composite", n);
}

function verifyPocklington(cert, depth) {
  const n = num(cert.n, "n");
  const M = num(cert.M, "M");
  if (M <= 1n || (n - 1n) % M !== 0n) return fail("M does not divide n-1");
  const R = (n - 1n) / M;
  if (gcd(M, R) !== 1n) return fail("gcd(M, R) is not 1");
  let built = 1n;
  for (const factor of cert.factors ?? []) {
    const q = num(factor.q, "q");
    const checked = verify(factor.cert, depth + 1);
    if (!checked.ok || checked.status !== "prime" || checked.n !== q) {
      return fail(`prime certificate failed for ${factor.q}`);
    }
    built *= q ** BigInt(factor.e);
  }
  if (built !== M) return fail("factorization does not rebuild M");
  for (const factor of cert.factors) {
    const q = BigInt(factor.q);
    const qe = q ** BigInt(factor.e);
    const base = (cert.bases ?? []).find((item) => item.q === factor.q && item.e === factor.e);
    if (!base) return fail(`missing base for ${factor.q}^${factor.e}`);
    const a = num(base.a, "a");
    if (a <= 1n || a >= n || gcd(a, n) !== 1n) return fail("bad base");
    if (modPow(a, n - 1n, n) !== 1n) return fail("a^(n-1) is not 1");
    if (gcd(modPow(a, (n - 1n) / qe, n) - 1n, n) !== 1n) {
      return fail("gcd condition failed");
    }
  }
  if (cert.tier === "sqrt") {
    return M * M > n ? ok("prime", n) : fail("M is not above sqrt(n)");
  }
  if (M * M * M <= n || M * M > n) return fail("cube-root tier does not apply");
  const c2 = (n - 1n) / (M * M);
  const c1 = ((n - 1n) / M) % M;
  if (cert.c1 !== c1.toString(10) || cert.c2 !== c2.toString(10)) return fail("c1/c2 mismatch");
  if (isSquare(c1 * c1 - 4n * c2)) return fail("discriminant is square");
  return ok("prime", n);
}

const file = process.argv[2];
if (!file) {
  console.error("usage: node verify.mjs certificate.json");
  process.exit(2);
}
const cert = JSON.parse(await readFile(file, "utf8"));
const result = verify(cert);
if (!result.ok) {
  console.error("REJECT", result.reason);
  process.exit(1);
}
console.log(result.status, result.n.toString(10));
