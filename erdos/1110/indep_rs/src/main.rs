//! Clean-room checker for the Erdős #1110 look-ahead potential certificates.
//! Written from SPEC.md only.
//!
//! Internal indexing: every per-state array (W, Vi, bad flags) is stored at the
//! "transposed" index  tidx(x) = (x mod B^(D-s)) * P + floor(x / B^(D-s)).
//! This is a bijection on [0, M) (pure implementation detail, chosen for cache
//! locality: for a fixed state and chain, the P successors over the fresh block u
//! differ only in their top s digits, so they occupy one contiguous P-block).

use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};
use rayon::prelude::*;
use sha2::{Digest, Sha256};
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
use std::time::Instant;

// ---------------------------------------------------------------- arithmetic

fn ipow(b: u64, e: u32) -> u64 {
    let mut r: u64 = 1;
    for _ in 0..e {
        r = r.checked_mul(b).expect("ipow overflow");
    }
    r
}
fn mulmod(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 * b as u128) % m as u128) as u64
}
fn powmod(b: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1 % m;
    let mut x = b % m;
    while e > 0 {
        if e & 1 == 1 {
            r = mulmod(r, x, m);
        }
        x = mulmod(x, x, m);
        e >>= 1;
    }
    r
}
fn modinv(a: u64, m: u64) -> u64 {
    let (mut old_r, mut r) = (a as i128 % m as i128, m as i128);
    let (mut old_s, mut s) = (1i128, 0i128);
    while r != 0 {
        let q = old_r / r;
        (old_r, r) = (r, old_r - q * r);
        (old_s, s) = (s, old_s - q * s);
    }
    assert_eq!(old_r, 1, "not invertible");
    let inv = old_s.rem_euclid(m as i128) as u64;
    assert_eq!(mulmod(inv, a % m, m), 1 % m);
    inv
}
fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        ((self.next() as u128 * n as u128) >> 64) as u64
    }
}

// ---------------------------------------------------------------- bit arrays

struct ABits(Vec<AtomicU64>);
impl ABits {
    fn new(n: u64) -> Self {
        ABits((0..n.div_ceil(64)).map(|_| AtomicU64::new(0)).collect())
    }
    #[inline(always)]
    fn get(&self, i: u64) -> bool {
        (self.0[(i >> 6) as usize].load(Relaxed) >> (i & 63)) & 1 == 1
    }
    #[inline(always)]
    fn set(&self, i: u64) {
        self.0[(i >> 6) as usize].fetch_or(1 << (i & 63), Relaxed);
    }
    #[inline(always)]
    fn clear(&self, i: u64) {
        self.0[(i >> 6) as usize].fetch_and(!(1 << (i & 63)), Relaxed);
    }
    fn zero(&self) {
        self.0.par_iter().for_each(|w| w.store(0, Relaxed));
    }
    fn count(&self) -> u64 {
        self.0.par_iter().map(|w| w.load(Relaxed).count_ones() as u64).sum()
    }
    fn into_plain(self) -> Vec<u64> {
        self.0.into_iter().map(|a| a.into_inner()).collect()
    }
}
#[inline(always)]
fn pget(b: &[u64], i: u64) -> bool {
    (b[(i >> 6) as usize] >> (i & 63)) & 1 == 1
}

// ---------------------------------------------------------------- instance

#[derive(Clone, Copy, Debug)]
struct Params {
    b: u64,
    q: u64,
    s: u32,
    d: u32,
    h: u32,
    slack: u32,
}

#[derive(Clone, Debug)]
struct Chain {
    amask: u32,
    gmask: u32,
    v: u64,
    h: u32,
}

#[derive(Clone, Debug)]
struct KC {
    v: u64,
    h: u32,
    qh: u64,    // Q^h mod M
    qhp: u64,   // Q^h mod P
    qinvh: u64, // Q^{-h} mod M
}

struct Inst {
    pr: Params,
    p: u64,
    m: u64,
    mp: u64,
    bds: u64,
    qinv_mp: u64,
    qinv_m: u64,
    q_m: u64,
    chains: Vec<Chain>,
    hmin: Vec<Option<u32>>,
    kept: Vec<Vec<KC>>,
    kept_flat: Vec<KC>,
    kept_raw: usize, // kept chains before (v,h)-dedup
}

fn bits_asc(mask: u32) -> Vec<u32> {
    (0..32).filter(|i| mask >> i & 1 == 1).collect()
}

impl Inst {
    fn new(pr: Params) -> Inst {
        assert!(pr.b >= 2 && pr.q >= 2 && pr.s >= 1 && pr.d >= pr.s);
        assert_eq!(gcd(pr.b, pr.q), 1, "B, Q must be coprime");
        assert!(pr.s <= 16 && pr.h <= 24);
        let p = ipow(pr.b, pr.s);
        let m = ipow(pr.b, pr.d);
        let mp = ipow(pr.b, pr.d + pr.s);
        assert!(mp < (1u64 << 62));
        assert!(m < (1u64 << 32), "M must be < 2^32 so Q^h*(r/P) fits in u64");
        assert!(p <= 4096);
        let bds = ipow(pr.b, pr.d - pr.s);
        let qinv_mp = modinv(pr.q, mp);
        let qinv_m = modinv(pr.q, m);
        // all chains
        let mut chains = Vec::new();
        let bpow: Vec<u64> = (0..pr.s).map(|a| powmod(pr.b, a as u64, mp)).collect();
        let qip: Vec<u64> = (0..pr.h).map(|g| powmod(qinv_mp, g as u64, mp)).collect();
        for amask in 0u32..(1 << pr.s) {
            let k = amask.count_ones();
            if k > pr.h {
                continue;
            }
            let al = bits_asc(amask);
            for gmask in 0u32..(1 << pr.h) {
                if gmask.count_ones() != k {
                    continue;
                }
                let gl = bits_asc(gmask);
                let mut v = 0u64;
                for i in 0..k as usize {
                    v = (v + mulmod(bpow[al[i] as usize], qip[gl[i] as usize], mp)) % mp;
                }
                let h = if k == 0 { 0 } else { gl[k as usize - 1] + 1 };
                chains.push(Chain { amask, gmask, v, h });
            }
        }
        let mut hmin: Vec<Option<u32>> = vec![None; p as usize];
        for c in &chains {
            let cl = (c.v % p) as usize;
            hmin[cl] = Some(hmin[cl].map_or(c.h, |x| x.min(c.h)));
        }
        let mut kept: Vec<Vec<KC>> = vec![Vec::new(); p as usize];
        let mut kept_raw = 0;
        let mut kv: Vec<Vec<(u64, u32)>> = vec![Vec::new(); p as usize];
        for c in &chains {
            let cl = (c.v % p) as usize;
            if c.h <= hmin[cl].unwrap() + pr.slack {
                kv[cl].push((c.v, c.h));
                kept_raw += 1;
            }
        }
        for cl in 0..p as usize {
            kv[cl].sort();
            kv[cl].dedup(); // identical (v,h) chains give identical transitions/costs
            // order by height so cheap chains come first (only affects speed)
            kv[cl].sort_by_key(|&(v, h)| (h, v));
            for &(v, h) in &kv[cl] {
                kept[cl].push(KC {
                    v,
                    h,
                    qh: powmod(pr.q, h as u64, m),
                    qhp: powmod(pr.q, h as u64, p),
                    qinvh: powmod(qinv_m, h as u64, m),
                });
            }
        }
        let kept_flat = kept.iter().flatten().cloned().collect();
        Inst {
            pr,
            p,
            m,
            mp,
            bds,
            qinv_mp,
            qinv_m,
            q_m: pr.q % m,
            chains,
            hmin,
            kept,
            kept_flat,
            kept_raw,
        }
    }

    #[inline(always)]
    fn tidx(&self, x: u64) -> u64 {
        (x % self.bds) * self.p + x / self.bds
    }
    #[inline(always)]
    fn xof(&self, i: u64) -> u64 {
        (i % self.p) * self.bds + i / self.p
    }

    /// The transition exactly as written in the spec (u128 arithmetic).
    fn next_literal(&self, x: u64, u: u64, v: u64, h: u32) -> u64 {
        assert!(x < self.m && u < self.p && v < self.mp);
        let z = x as u128 + self.m as u128 * u as u128;
        assert!(z < self.mp as u128);
        let mp = self.mp as u128;
        let r = (z + mp - v as u128) % mp;
        assert!(r % self.p as u128 == 0, "r not divisible by P");
        let qh = powmod(self.pr.q, h as u64, self.m) as u128;
        ((qh * (r / self.p as u128)) % self.m as u128) as u64
    }

    /// For state x and kept chain kc (of class x mod P): returns (base, top0)
    /// such that the internal index of next(x,u,kc) is base + ((top0 + u*qhp) mod P).
    /// next(u=0) is computed literally (with the divisibility assert); the u-step uses
    /// r(u)/P = r(0)/P + u*B^(D-s) (mod M) and Q^h*B^(D-s)*u = B^(D-s)*(Q^h u mod P) (mod M).
    #[inline(always)]
    fn start(&self, x: u64, kc: &KC) -> (u64, u64) {
        let t = (x + self.mp - kc.v) % self.mp;
        assert!(t % self.p == 0, "r not divisible by P");
        let n0 = (kc.qh * (t / self.p)) % self.m;
        ((n0 % self.bds) * self.p, n0 / self.bds)
    }

    fn covered(&self, c: u64) -> bool {
        self.hmin[c as usize].is_some()
    }
}

// ---------------------------------------------------------------- viable set W

struct WStats {
    passes: Vec<(bool, u64)>, // (full pass?, removed)
}

fn check_x(inst: &Inst, w: &ABits, x: u64) -> bool {
    let p = inst.p;
    let qx = mulmod(inst.q_m, x, inst.m);
    if !w.get(inst.tidx(qx)) {
        return false;
    }
    let c = (x % p) as usize;
    let mut cov = [0u64; 64];
    let mut cnt = 0u64;
    for kc in &inst.kept[c] {
        let (base, mut top) = inst.start(x, kc);
        for u in 0..p {
            let wd = (u >> 6) as usize;
            let bt = 1u64 << (u & 63);
            if cov[wd] & bt == 0 && w.get(base + top) {
                cov[wd] |= bt;
                cnt += 1;
            }
            top += kc.qhp;
            if top >= p {
                top -= p;
            }
        }
        if cnt == p {
            return true;
        }
    }
    false
}

fn compute_w(inst: &Inst, use_dirty: bool, verbose: bool) -> (Vec<u64>, WStats) {
    let m = inst.m;
    let w = ABits::new(m);
    w.0.par_iter().enumerate().for_each(|(wi, word)| {
        let mut bits = 0u64;
        for j in 0..64u64 {
            let i = wi as u64 * 64 + j;
            if i < m && inst.covered(inst.xof(i) % inst.p) {
                bits |= 1 << j;
            }
        }
        word.store(bits, Relaxed);
    });
    if verbose {
        eprintln!("  W init (covered classes): {}", w.count());
    }
    let mut dcur = ABits::new(if use_dirty { m } else { 1 });
    let mut dnext = ABits::new(if use_dirty { m } else { 1 });
    let mut full = true;
    let mut stats = WStats { passes: vec![] };
    loop {
        let t0 = Instant::now();
        let removed: u64 = (0..m as usize)
            .into_par_iter()
            .map(|x| x as u64)
            .with_min_len(1 << 12)
            .map(|x| {
                if !full && !dcur.get(x) {
                    return 0u64;
                }
                let i = inst.tidx(x);
                if !w.get(i) || check_x(inst, &w, x) {
                    return 0;
                }
                w.clear(i);
                if use_dirty {
                    // every predecessor of x: Q^{-1}x (rule ii) and one per kept chain (rule i)
                    dnext.set(mulmod(inst.qinv_m, x, m));
                    for kc in &inst.kept_flat {
                        let q = mulmod(kc.qinvh, x, m);
                        let z = (inst.p * q + kc.v) % inst.mp;
                        dnext.set(z % m);
                    }
                }
                1
            })
            .sum();
        stats.passes.push((full, removed));
        if verbose {
            eprintln!(
                "  pass {} ({}) removed {} [{:.1}s]",
                stats.passes.len(),
                if full { "full" } else { "dirty" },
                removed,
                t0.elapsed().as_secs_f64()
            );
        }
        if removed == 0 {
            if full {
                break;
            }
            full = true;
            continue;
        }
        if use_dirty {
            std::mem::swap(&mut dcur, &mut dnext);
            dnext.zero();
            full = false;
        }
    }
    (w.into_plain(), stats)
}

// ---------------------------------------------------------------- potential

struct Pot {
    vi: Vec<i64>,  // internal index
    bad: Vec<u64>, // bits, internal index: non-finite or |V| >= 1e5
    sha: String,
}

fn sha_hex(bytes: &[u8]) -> String {
    let d = Sha256::digest(bytes);
    d.iter().map(|b| format!("{:02x}", b)).collect()
}

/// layout_t: true = transposed (spec), false = natural (value of x at index x)
fn load_pot(inst: &Inst, bytes: &[u8], layout_t: bool) -> Pot {
    let m = inst.m;
    assert_eq!(bytes.len() as u64, 4 * m, "potential file must hold exactly M float32 values");
    let sha = sha_hex(bytes);
    let vi: Vec<i64> = (0..m)
        .into_par_iter()
        .map(|i| {
            let x = inst.xof(i);
            let fi = if layout_t { inst.tidx(x) } else { x } as usize;
            let f = f32::from_le_bytes(bytes[4 * fi..4 * fi + 4].try_into().unwrap());
            // half away from zero; a non-finite V is "bad" and gets Vi = 0 by convention
            if f.is_finite() { ((f as f64) * 1048576.0).round() as i64 } else { 0 }
        })
        .collect();
    let nw = m.div_ceil(64);
    let bad: Vec<u64> = (0..nw)
        .into_par_iter()
        .map(|wi| {
            let mut bits = 0u64;
            for j in 0..64 {
                let i = wi * 64 + j;
                if i >= m {
                    break;
                }
                let x = inst.xof(i);
                let fi = if layout_t { inst.tidx(x) } else { x } as usize;
                let f = f32::from_le_bytes(bytes[4 * fi..4 * fi + 4].try_into().unwrap());
                if !f.is_finite() || (f as f64).abs() >= 1e5 {
                    bits |= 1 << j;
                }
            }
            bits
        })
        .collect();
    Pot { vi, bad, sha }
}

fn d_of(inst: &Inst, w: &[u64], pot: &Pot, x: u64, best: &mut [i64]) -> i64 {
    let p = inst.p;
    let c = (x % p) as usize;
    best[..p as usize].fill(i64::MAX);
    for kc in &inst.kept[c] {
        let hc = (kc.h as i64) << 20;
        let (base, mut top) = inst.start(x, kc);
        for u in 0..p as usize {
            let i = base + top;
            if pget(w, i) {
                let val = hc + pot.vi[i as usize];
                if val < best[u] {
                    best[u] = val;
                }
            }
            top += kc.qhp;
            if top >= p {
                top -= p;
            }
        }
    }
    let mut sum = 0i64;
    for u in 0..p as usize {
        assert!(best[u] != i64::MAX, "empty min (x not viable?)");
        sum += best[u];
    }
    sum - (p as i64) * pot.vi[inst.tidx(x) as usize]
}

#[derive(Debug, Clone, Copy)]
struct Red {
    gnum: i64,
    argmax: u64,
    bad: u64,
    nw: u64,
}

fn potential_pass(inst: &Inst, w: &[u64], pot: &Pot) -> Red {
    let ident = || Red { gnum: i64::MIN, argmax: u64::MAX, bad: 0, nw: 0 };
    let comb = |a: Red, b: Red| {
        let (gnum, argmax) = if a.gnum > b.gnum || (a.gnum == b.gnum && a.argmax < b.argmax) {
            (a.gnum, a.argmax)
        } else {
            (b.gnum, b.argmax)
        };
        Red { gnum, argmax, bad: a.bad + b.bad, nw: a.nw + b.nw }
    };
    (0..inst.m as usize)
        .into_par_iter()
        .map(|x| x as u64)
        .with_min_len(1 << 10)
        .fold(
            || (ident(), vec![0i64; inst.p as usize]),
            |(acc, mut best): (Red, Vec<i64>), x: u64| {
                let i = inst.tidx(x);
                if !pget(w, i) {
                    return (acc, best);
                }
                let d = d_of(inst, w, pot, x, &mut best);
                let one = Red { gnum: d, argmax: x, bad: pget(&pot.bad, i) as u64, nw: 1 };
                (comb(acc, one), best)
            },
        )
        .map(|(a, _)| a)
        .reduce(ident, comb)
}

// ---------------------------------------------------------------- independent naive path (self-tests)

/// Chains by DFS over strictly increasing pairs (independent of the bitmask enumeration).
/// Returns (alphas, gammas, h, class) with class computed via big integers and a
/// brute-force inverse of Q modulo P.
fn dfs_chains(pr: &Params) -> Vec<(Vec<u32>, Vec<u32>, u32, u64)> {
    let p = ipow(pr.b, pr.s);
    let qinv_p = (0..p).find(|t| (pr.q % p) * t % p == 1 % p).unwrap();
    let mut out = Vec::new();
    fn rec(
        pr: &Params,
        p: u64,
        qinv_p: u64,
        a: &mut Vec<u32>,
        g: &mut Vec<u32>,
        out: &mut Vec<(Vec<u32>, Vec<u32>, u32, u64)>,
    ) {
        let h = g.last().map_or(0, |x| x + 1);
        // S = sum B^a Q^{h-g} is the integer Q^h * (chain value); class = S * Q^{-h} mod P
        let mut s = BigUint::zero();
        for i in 0..a.len() {
            s += BigUint::from(pr.b).pow(a[i]) * BigUint::from(pr.q).pow(h - g[i]);
        }
        let sp = (s % BigUint::from(p)).to_u64().unwrap();
        let mut cl = sp;
        for _ in 0..h {
            cl = cl * qinv_p % p;
        }
        out.push((a.clone(), g.clone(), h, cl));
        let a0 = a.last().map_or(0, |x| x + 1);
        let g0 = g.last().map_or(0, |x| x + 1);
        for na in a0..pr.s {
            for ng in g0..pr.h {
                a.push(na);
                g.push(ng);
                rec(pr, p, qinv_p, a, g, out);
                a.pop();
                g.pop();
            }
        }
    }
    rec(pr, p, qinv_p, &mut vec![], &mut vec![], &mut out);
    out
}

/// Direct big-integer transition: window z = low D+s digits of Y; returns the low D digits
/// of (Q^h*Y - sum_i B^{a_i} Q^{h-g_i}) / P  (asserting the division is exact).
fn big_next(pr: &Params, y: &BigInt, a: &[u32], g: &[u32], h: u32) -> u64 {
    let p = BigInt::from(ipow(pr.b, pr.s));
    let m = BigInt::from(ipow(pr.b, pr.d));
    let mut n = BigInt::from(pr.q).pow(h) * y;
    for i in 0..a.len() {
        n -= BigInt::from(pr.b).pow(a[i]) * BigInt::from(pr.q).pow(h - g[i]);
    }
    let (qt, rm) = n.div_mod_floor(&p);
    assert!(rm.is_zero(), "big: not divisible by P");
    qt.mod_floor(&m).to_u64().unwrap()
}

struct Naive {
    w: Vec<bool>,
    d: Vec<Option<i64>>,
    gnum: Option<i64>,
    bad: u64,
}

fn naive_all(pr: &Params, vfile: Option<(&[u8], bool)>, rng: &mut Rng) -> Naive {
    let p = ipow(pr.b, pr.s);
    let m = ipow(pr.b, pr.d);
    let mp = ipow(pr.b, pr.d + pr.s);
    let chains = dfs_chains(pr);
    let mut hmin = vec![u32::MAX; p as usize];
    for c in &chains {
        hmin[c.3 as usize] = hmin[c.3 as usize].min(c.2);
    }
    let kept: Vec<&(Vec<u32>, Vec<u32>, u32, u64)> =
        chains.iter().filter(|c| c.2 <= hmin[c.3 as usize].saturating_add(pr.slack)).collect();
    // transition table via big integers, Y = z + M' * (random high part)
    let mut nxt: Vec<Vec<Vec<(u32, u64)>>> = vec![vec![]; m as usize]; // [x][u] -> (h,next)
    for x in 0..m {
        for u in 0..p {
            let z = x + m * u;
            let hi = BigInt::from(rng.next()) * BigInt::from(rng.next());
            let y = BigInt::from(z) + BigInt::from(mp) * hi;
            let mut lst = vec![];
            for c in kept.iter().filter(|c| c.3 == x % p) {
                lst.push((c.2, big_next(pr, &y, &c.0, &c.1, c.2)));
            }
            nxt[x as usize].push(lst);
        }
    }
    let mut w: Vec<bool> = (0..m).map(|x| hmin[(x % p) as usize] != u32::MAX).collect();
    loop {
        let mut nw = w.clone();
        for x in 0..m as usize {
            if !w[x] {
                continue;
            }
            let ok2 = w[((pr.q as u128 * x as u128) % m as u128) as usize];
            let ok1 = (0..p as usize).all(|u| nxt[x][u].iter().any(|&(_, n)| w[n as usize]));
            if !(ok1 && ok2) {
                nw[x] = false;
            }
        }
        if nw == w {
            break;
        }
        w = nw;
    }
    let mut d = vec![None; m as usize];
    let mut gnum = None;
    let mut bad = 0;
    if let Some((bytes, layout_t)) = vfile {
        let bds = ipow(pr.b, pr.d - pr.s);
        let vx = |x: u64| -> f32 {
            let fi = if layout_t { (x % bds) * p + x / bds } else { x } as usize;
            f32::from_le_bytes(bytes[4 * fi..4 * fi + 4].try_into().unwrap())
        };
        let vi = |x: u64| -> i64 {
            let f = vx(x);
            if f.is_finite() { (f as f64 * 1048576.0).round() as i64 } else { 0 }
        };
        for x in 0..m {
            if !w[x as usize] {
                continue;
            }
            let f = vx(x);
            if !f.is_finite() || (f as f64).abs() >= 1e5 {
                bad += 1;
            }
            let mut tot = 0i64;
            for u in 0..p as usize {
                let mn = nxt[x as usize][u]
                    .iter()
                    .filter(|&&(_, n)| w[n as usize])
                    .map(|&(h, n)| ((h as i64) << 20) + vi(n))
                    .min()
                    .unwrap();
                tot += mn;
            }
            let dx = tot - p as i64 * vi(x);
            d[x as usize] = Some(dx);
            gnum = Some(gnum.map_or(dx, |g: i64| g.max(dx)));
        }
    }
    Naive { w, d, gnum, bad }
}

// ---------------------------------------------------------------- self-tests

fn binom(n: u64, k: u64) -> u64 {
    if k > n {
        return 0;
    }
    let mut r = 1u64;
    for i in 0..k {
        r = r * (n - i) / (i + 1);
    }
    r
}

fn selftest_transition(pr: Params, trials: usize, rng: &mut Rng) {
    let inst = Inst::new(pr);
    let mut checked = 0;
    for _ in 0..trials {
        let c = &inst.chains[rng.below(inst.chains.len() as u64) as usize];
        let cl = c.v % inst.p;
        let x = (rng.below(inst.m) / inst.p) * inst.p + cl;
        let u = rng.below(inst.p);
        let lit = inst.next_literal(x, u, c.v, c.h);
        let a = bits_asc(c.amask);
        let g = bits_asc(c.gmask);
        let z = x + inst.m * u;
        for rep in 0..3 {
            // Y with random high digits beyond the D+s window (rep 0: none)
            let hi = if rep == 0 {
                BigInt::zero()
            } else {
                BigInt::from(rng.next()) * BigInt::from(rng.next()) + BigInt::from(rng.next())
            };
            let y = BigInt::from(z) + BigInt::from(inst.mp) * hi;
            let big = big_next(&pr, &y, &a, &g, c.h);
            assert_eq!(lit, big, "literal vs big-int transition mismatch {:?} x={} u={}", pr, x, u);
        }
        // fast internal-index path
        let kc = KC {
            v: c.v,
            h: c.h,
            qh: powmod(pr.q, c.h as u64, inst.m),
            qhp: powmod(pr.q, c.h as u64, inst.p),
            qinvh: powmod(inst.qinv_m, c.h as u64, inst.m),
        };
        let (base, top0) = inst.start(x, &kc);
        let top = (top0 + u * kc.qhp) % inst.p;
        assert_eq!(inst.xof(base + top), lit, "fast index path mismatch");
        assert_eq!(inst.tidx(lit), base + top);
        // predecessor formula used for dirty-marking: from y=lit recover (x,u)
        let q = mulmod(kc.qinvh, lit, inst.m);
        let zz = (inst.p * q + kc.v) % inst.mp;
        assert_eq!(zz % inst.m, x, "predecessor formula mismatch");
        assert_eq!(zz / inst.m, u);
        checked += 1;
    }
    println!("  [T1] transition {:?}: {} random (x,u,chain) triples x 3 high-digit draws OK", pr, checked);
}

fn selftest_chains(pr: Params) {
    let inst = Inst::new(pr);
    let dfs = dfs_chains(&pr);
    let expect: u64 = (0..=pr.s.min(pr.h) as u64).map(|k| binom(pr.s as u64, k) * binom(pr.h as u64, k)).sum();
    assert_eq!(inst.chains.len() as u64, expect, "chain count vs binomial formula");
    assert_eq!(dfs.len() as u64, expect, "dfs chain count vs binomial formula");
    let p = inst.p as usize;
    let mut cnt_a = vec![0u64; p];
    let mut cnt_b = vec![0u64; p];
    let mut hm_b = vec![u32::MAX; p];
    for c in &inst.chains {
        cnt_a[(c.v % inst.p) as usize] += 1;
    }
    for c in &dfs {
        cnt_b[c.3 as usize] += 1;
        hm_b[c.3 as usize] = hm_b[c.3 as usize].min(c.2);
    }
    assert_eq!(cnt_a, cnt_b, "per-class chain counts differ");
    for cl in 0..p {
        assert_eq!(inst.hmin[cl].unwrap_or(u32::MAX), hm_b[cl], "hmin differs at class {}", cl);
    }
    // full value check: Q^h * v == sum B^a Q^{h-g}  (mod M') for each chain
    let mpb = BigUint::from(inst.mp);
    for c in &inst.chains {
        let (a, g) = (bits_asc(c.amask), bits_asc(c.gmask));
        let mut s = BigUint::zero();
        for i in 0..a.len() {
            s += BigUint::from(pr.b).pow(a[i]) * BigUint::from(pr.q).pow(c.h - g[i]);
        }
        let lhs = (BigUint::from(pr.q).pow(c.h) * BigUint::from(c.v)) % &mpb;
        assert_eq!(lhs, s % &mpb, "chain value mismatch");
    }
    let uncovered = (0..p).filter(|&cl| cnt_b[cl] == 0).count();
    println!(
        "  [T2] chains {:?}: total {} (= sum C(s,k)C(H,k)), per-class counts and hmin agree with DFS; {} uncovered classes; kept {} ({} distinct (v,h))",
        pr,
        expect,
        uncovered,
        inst.kept_raw,
        inst.kept_flat.len()
    );
}

fn selftest_full(pr: Params, rng: &mut Rng, mode: &str) {
    let inst = Inst::new(pr);
    let m = inst.m;
    // build a V file
    let mut vals: Vec<f32> = (0..m)
        .map(|_| match mode {
            "zero" => 0.0f32,
            _ => ((rng.below(2_000_001) as f64 - 1_000_000.0) / 37.0) as f32 / 7.0,
        })
        .collect();
    if mode == "bad" {
        vals[rng.below(m) as usize] = f32::NAN;
        vals[rng.below(m) as usize] = 2.5e5;
        vals[rng.below(m) as usize] = f32::INFINITY;
    }
    if mode == "half" {
        // exact half-ulps of 2^-20 to exercise round-half-away-from-zero
        for v in vals.iter_mut() {
            *v = ((rng.below(2001) as f64 - 1000.0 + 0.5) / 1048576.0) as f32;
        }
    }
    let bytes: Vec<u8> = vals.iter().flat_map(|v| v.to_le_bytes()).collect();
    for &layout_t in &[true, false] {
        let nv = naive_all(&pr, Some((&bytes, layout_t)), rng);
        for &dirty in &[true, false] {
            let (w, _st) = compute_w(&inst, dirty, false);
            for x in 0..m {
                assert_eq!(pget(&w, inst.tidx(x)), nv.w[x as usize], "W differs at x={} {:?}", x, pr);
            }
            let nw = nv.w.iter().filter(|&&b| b).count() as u64;
            if nw == 0 {
                continue;
            }
            let pot = load_pot(&inst, &bytes, layout_t);
            let mut best = vec![0i64; inst.p as usize];
            for x in 0..m {
                if nv.w[x as usize] {
                    let d = d_of(&inst, &w, &pot, x, &mut best);
                    assert_eq!(Some(d), nv.d[x as usize], "d differs at x={}", x);
                    if mode == "zero" {
                        assert_eq!(d % (1 << 20), 0);
                    }
                }
            }
            let r = potential_pass(&inst, &w, &pot);
            assert_eq!(Some(r.gnum), nv.gnum);
            assert_eq!(r.bad, nv.bad);
            assert_eq!(r.nw, nw);
            assert_eq!(nv.d[r.argmax as usize], Some(r.gnum));
        }
        let nw = nv.w.iter().filter(|&&b| b).count();
        let ncov = (0..m).filter(|&x| inst.covered(x % inst.p)).count();
        println!(
            "  [T3] full {:?} V={} layout={}: |W|={} (covered {}, removed {}), GNUM={:?}{}, bad={} — fast == naive (W, every d(x), GNUM, bad; dirty and full-pass W)",
            pr,
            mode,
            if layout_t { "T" } else { "N" },
            nw,
            ncov,
            ncov - nw,
            nv.gnum,
            nv.gnum.map_or(String::new(), |g| format!(" (= {}*2^20{})", g >> 20, if g % (1 << 20) == 0 { "" } else { "+frac" })),
            nv.bad
        );
    }
}

fn selftests() {
    let mut rng = Rng(0x1110_2026);
    let t0 = Instant::now();
    println!("== Self-test 1: transition vs big-integer direct computation");
    let tiny = [
        Params { b: 4, q: 3, s: 1, d: 3, h: 4, slack: 0 },
        Params { b: 2, q: 9, s: 1, d: 5, h: 4, slack: 0 },
        Params { b: 4, q: 3, s: 2, d: 4, h: 5, slack: 0 },
        Params { b: 2, q: 7, s: 3, d: 6, h: 3, slack: 0 },
        Params { b: 3, q: 5, s: 1, d: 4, h: 4, slack: 0 },
        Params { b: 5, q: 2, s: 2, d: 3, h: 3, slack: 0 },
    ];
    for pr in tiny {
        selftest_transition(pr, 3000, &mut rng);
    }
    let real = [
        Params { b: 4, q: 3, s: 2, d: 14, h: 18, slack: 12 },
        Params { b: 2, q: 9, s: 1, d: 26, h: 12, slack: 7 },
        Params { b: 3, q: 5, s: 1, d: 17, h: 12, slack: 7 },
        Params { b: 2, q: 7, s: 11, d: 22, h: 10, slack: 3 },
    ];
    for pr in real {
        selftest_transition(pr, 3000, &mut rng);
    }
    println!("== Self-test 2: chain enumeration vs independent DFS enumeration");
    for pr in tiny.iter().chain(real.iter()) {
        selftest_chains(*pr);
    }
    println!("== Self-test 3: full pipeline (fast) vs naive big-integer implementation on tiny cases");
    let full = [
        Params { b: 4, q: 3, s: 1, d: 3, h: 4, slack: 0 },
        Params { b: 4, q: 3, s: 1, d: 3, h: 4, slack: 2 },
        Params { b: 2, q: 9, s: 1, d: 5, h: 4, slack: 1 },
        Params { b: 2, q: 9, s: 1, d: 7, h: 3, slack: 7 },
        Params { b: 4, q: 3, s: 2, d: 4, h: 5, slack: 2 },
        Params { b: 2, q: 7, s: 3, d: 6, h: 3, slack: 1 },
        Params { b: 2, q: 7, s: 4, d: 7, h: 4, slack: 3 },
        Params { b: 3, q: 5, s: 1, d: 5, h: 4, slack: 1 },
        Params { b: 2, q: 3, s: 2, d: 7, h: 4, slack: 0 },
        Params { b: 5, q: 2, s: 1, d: 3, h: 3, slack: 0 },
        Params { b: 2, q: 5, s: 1, d: 6, h: 2, slack: 0 },
        // the real instances' (B,Q,s,H,SLACK) with small D
        Params { b: 4, q: 3, s: 2, d: 5, h: 18, slack: 12 },
        Params { b: 2, q: 9, s: 1, d: 10, h: 12, slack: 7 },
        Params { b: 3, q: 5, s: 1, d: 7, h: 12, slack: 7 },
        Params { b: 2, q: 7, s: 5, d: 9, h: 6, slack: 3 },
    ];
    for pr in full {
        selftest_full(pr, &mut rng, "zero");
    }
    for pr in full {
        selftest_full(pr, &mut rng, "rand");
    }
    // grid search for tiny instances where W is a proper nonempty subset of the covered states
    // (so the removal iteration is genuinely exercised), then fast-vs-naive on them
    let mut partial = vec![];
    for &(b, q) in &[(2u64, 3u64), (2, 5), (2, 7), (2, 9), (3, 2), (3, 5), (4, 3), (5, 3), (3, 4)] {
        for s_ in 1..=3u32 {
            for d_ in s_..=12u32 {
                if ipow(b, d_ + s_) > 1 << 14 || ipow(b, d_) < 8 {
                    continue;
                }
                for h_ in 1..=8u32 {
                    for sl in 0..=3u32 {
                        let pr = Params { b, q, s: s_, d: d_, h: h_, slack: sl };
                        let inst = Inst::new(pr);
                        let (w, _) = compute_w(&inst, true, false);
                        let nw: u64 = w.iter().map(|x| x.count_ones() as u64).sum();
                        let ncov = (0..inst.m).filter(|&x| inst.covered(x % inst.p)).count() as u64;
                        if nw > 0 && nw < ncov {
                            partial.push(pr);
                        }
                    }
                }
            }
        }
    }
    println!("  grid: {} tiny parameter sets with 0 < |W| < #covered; testing up to 40 of them", partial.len());
    // spread the picks over (B,Q,s) families: at most 4 per family
    let mut picked: Vec<Params> = vec![];
    let mut fam: std::collections::HashMap<(u64, u64, u32), usize> = Default::default();
    for pr in &partial {
        let e = fam.entry((pr.b, pr.q, pr.s)).or_insert(0);
        if *e < 4 && picked.len() < 40 {
            *e += 1;
            picked.push(*pr);
        }
    }
    println!("  grid families with partial W: {:?}", { let mut k: Vec<_> = fam.keys().cloned().collect(); k.sort(); k });
    for pr in &picked {
        selftest_full(*pr, &mut rng, "rand");
    }
    for pr in picked.iter().take(5) {
        selftest_full(*pr, &mut rng, "bad");
        selftest_full(*pr, &mut rng, "zero");
    }
    selftest_full(full[4], &mut rng, "bad");
    selftest_full(full[2], &mut rng, "half");
    // rounding sanity
    for (f, e) in [(0.5f64, 1i64), (-0.5, -1), (1.5, 2), (-2.5, -3), (2.4, 2)] {
        assert_eq!(((f / 1048576.0) as f32 as f64 * 1048576.0).round() as i64, e);
    }
    println!("ALL SELF-TESTS PASSED in {:.1}s", t0.elapsed().as_secs_f64());
}

// ---------------------------------------------------------------- real run

fn dec(num: i128, den: i128, digits: usize) -> String {
    let neg = (num < 0) != (den < 0) && num != 0;
    let (n, d) = (num.abs(), den.abs());
    let mut s = format!("{}{}.", if neg { "-" } else { "" }, n / d);
    let mut r = n % d;
    for _ in 0..digits {
        r *= 10;
        s.push(char::from(b'0' + (r / d) as u8));
        r %= d;
    }
    s
}

fn run(args: &[String]) {
    // run NAME B Q s D H SLACK a b FILE LAYOUT(T|N) SHA_SPEC
    // SHA_SPEC: full hex | prefix:suffix | none
    let pa = |i: usize| -> u64 { args[i].parse().unwrap() };
    let name = &args[0];
    let pr = Params { b: pa(1), q: pa(2), s: pa(3) as u32, d: pa(4) as u32, h: pa(5) as u32, slack: pa(6) as u32 };
    let (la, lb) = (pa(7), pa(8));
    let file = &args[9];
    let layout_t = match args[10].as_str() {
        "T" => true,
        "N" => false,
        _ => panic!("layout T|N"),
    };
    let sha_spec = &args[11];
    let t0 = Instant::now();
    println!("=== instance {} {:?} lambda={}/{} layout={} file={}", name, pr, la, lb, args[10], file);
    let inst = Inst::new(pr);
    let ncls_cov = inst.hmin.iter().filter(|h| h.is_some()).count();
    println!(
        "P={} M={} M'={} chains={} covered classes={}/{} kept={} (distinct (v,h): {}) max kept/class={}",
        inst.p,
        inst.m,
        inst.mp,
        inst.chains.len(),
        ncls_cov,
        inst.p,
        inst.kept_raw,
        inst.kept_flat.len(),
        inst.kept.iter().map(|k| k.len()).max().unwrap()
    );
    // spot-check fast transition vs literal spec formula on the real parameters
    let mut rng = Rng(0xC0FFEE ^ inst.m);
    for _ in 0..200_000 {
        let cl = rng.below(inst.p) as usize;
        if inst.kept[cl].is_empty() {
            continue;
        }
        let kc = &inst.kept[cl][rng.below(inst.kept[cl].len() as u64) as usize];
        let x = (rng.below(inst.m) / inst.p) * inst.p + cl as u64;
        let u = rng.below(inst.p);
        let (base, top0) = inst.start(x, kc);
        assert_eq!(inst.xof(base + (top0 + u * kc.qhp) % inst.p), inst.next_literal(x, u, kc.v, kc.h));
    }
    println!("spot-check: 200000 random fast transitions == literal spec formula");
    // load + hash table
    let tl = Instant::now();
    let bytes = std::fs::read(file).expect("read table");
    let pot = load_pot(&inst, &bytes, layout_t);
    drop(bytes);
    let sha_ok = if sha_spec == "none" {
        None
    } else if let Some((pfx, sfx)) = sha_spec.split_once(':') {
        Some(pot.sha.starts_with(pfx) && pot.sha.ends_with(sfx))
    } else {
        Some(pot.sha == *sha_spec)
    };
    println!("table sha256 (uncompressed) = {}  expected={} match={:?} [{:.1}s]", pot.sha, sha_spec, sha_ok, tl.elapsed().as_secs_f64());
    if sha_ok == Some(false) {
        println!("SHA MISMATCH — aborting");
        std::process::exit(2);
    }
    // W
    let tw = Instant::now();
    let use_dirty = inst.kept_flat.len() <= 4096;
    let (w, st) = compute_w(&inst, use_dirty, true);
    let nw = w.iter().map(|x| x.count_ones() as u64).sum::<u64>();
    println!(
        "|W| = {}  (passes {}, dirty-propagation={}, removed total {}) [{:.1}s]",
        nw,
        st.passes.len(),
        use_dirty,
        st.passes.iter().map(|p| p.1).sum::<u64>(),
        tw.elapsed().as_secs_f64()
    );
    assert!(nw > 0, "W is empty");
    // potential
    let tp = Instant::now();
    let r = potential_pass(&inst, &w, &pot);
    assert_eq!(r.nw, nw);
    let den: i128 = inst.p as i128 * (1i128 << 20);
    let g = (r.gnum as i128).gcd(&den);
    let lt = (r.gnum as i128) * (lb as i128) < (la as i128) * den;
    let qa = BigUint::from(pr.q).pow(la as u32);
    let bsb = BigUint::from(pr.b).pow(pr.s * lb as u32);
    let argmax_digits: Vec<u64> = {
        let mut v = vec![];
        let mut t = r.argmax;
        for _ in 0..pr.d {
            v.push(t % pr.b);
            t /= pr.b;
        }
        v.reverse();
        v
    };
    println!("potential pass [{:.1}s]", tp.elapsed().as_secs_f64());
    println!("RESULT name={}", name);
    println!("RESULT layout={}", args[10]);
    println!("RESULT sha256={} sha_match={:?}", pot.sha, sha_ok);
    println!("RESULT W={}", nw);
    println!("RESULT bad={}", r.bad);
    println!("RESULT GNUM={}", r.gnum);
    println!("RESULT argmax={} (base-{} digits, most significant first: {:?})", r.argmax, pr.b, argmax_digits);
    println!(
        "RESULT g={}/{} = {}",
        r.gnum as i128 / g,
        den / g,
        dec(r.gnum as i128, den, 15)
    );
    println!("RESULT lambda={}/{} = {}", la, lb, dec(la as i128, lb as i128, 15));
    println!("RESULT g_lt_lambda={}  (GNUM*b < a*P*2^20)", lt);
    println!("RESULT Q^a<B^(s*b)={}  B^(s*b)<Q^a={}", qa < bsb, bsb < qa);
    println!("RESULT passes={:?}", st.passes);
    println!("RESULT runtime={:.1}s", t0.elapsed().as_secs_f64());
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(|s| s.as_str()) {
        Some("selftest") => selftests(),
        Some("run") => run(&args[2..]),
        Some("sha") => {
            let b = std::fs::read(&args[2]).unwrap();
            println!("{}  {}", sha_hex(&b), args[2]);
        }
        _ => eprintln!("usage: indep_rs selftest | run NAME B Q s D H SLACK a b FILE T|N SHA | sha FILE"),
    }
}

#[allow(dead_code)]
fn _unused(i: &Inst) -> (u64, &Vec<Chain>, BigInt) {
    (i.qinv_mp, &i.chains, BigInt::one().abs())
}
