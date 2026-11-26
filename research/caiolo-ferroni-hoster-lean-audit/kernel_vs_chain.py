#!/usr/bin/env python3
"""Independent semantic check of the Lean definitions used by counterexample_family.

From the CFH definitions only (no repo code):
  chi_st = sum_w mu_sw x^{rho_wt}            (Def 2.8)
  kappa  = (chi^rev)^sgn                     (Def 3.1)
  kbar_st = kappa_st/(x-1) (s<t), kbar_ss=-1 ; H* = -(kbar)^{-1}   (Def 2.4)
  f* = right KLS of kappa (Thm 2.3) -- we CHECK that f* = mu^sgn satisfies it
  F* = H* (f*)^rev                           (Def 2.7)
compare H*_{0,1}, F*_{0,1} with
  (a) the Lean chain formula  sum_S alpha(S) chowWeight / augmentedWeight  (CaioloFerroniHosterArithmetic.lean)
  (b) CFH Theorem 4.9 gamma expansion.
Polynomials are integer coefficient lists.  Lattices: Boolean, uniform, binary matroids.
"""
import itertools, random
from functools import lru_cache

# ---------- integer polynomial helpers ----------
def padd(a, b):
    n = max(len(a), len(b)); return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])
def pneg(a): return [-c for c in a]
def pmul(a, b):
    if not a or not b: return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b): out[i + j] += x * y
    return trim(out)
def trim(a):
    a = list(a)
    while a and a[-1] == 0: a.pop()
    return a
def rev(a, N):
    assert len(a) <= N + 1, 'degree exceeds reflection length'
    a = a + [0] * (N + 1 - len(a)); return trim(a[::-1])
def div_x_minus_1(a):
    # exact division by (x-1): synthetic division
    a = trim(a)
    if not a: return []
    n = len(a) - 1; q = [0] * n; r = 0
    for i in range(n, 0, -1):
        r = a[i] + r; q[i - 1] = r
    assert a[0] + r == 0, 'not divisible by x-1'
    return trim(q)
def geom(n): return [1] * n          # 1 + x + ... + x^{n-1}
def sc(c, a): return trim([c * x for x in a])

# ---------- lattices ----------
def lattice_from_flats(flats, rank):
    n = len(flats)
    le = [[flats[i] <= flats[j] for j in range(n)] for i in range(n)]
    return n, le, rank

def boolean(r):
    flats = [frozenset(S) for k in range(r + 1) for S in itertools.combinations(range(r), k)]
    return lattice_from_flats(flats, [len(F) for F in flats])

def uniform(r, n):
    flats = [frozenset(S) for k in range(r) for S in itertools.combinations(range(n), k)] + [frozenset(range(n))]
    return lattice_from_flats(flats, [len(F) if len(F) < r else r for F in flats])

def binary(vectors):
    """lattice of flats of the binary matroid on the given nonzero distinct vectors (ints as bitmasks)."""
    m = len(vectors)
    def rank(idx):
        basis = []
        for i in idx:
            v = vectors[i]
            for b in basis: v = min(v, v ^ b)
            if v: basis.append(v)
        return len(basis)
    def span_members(idx):
        # all vectors in the span, as set; members of ground set in it
        sp = {0}
        for i in idx:
            sp |= {s ^ vectors[i] for s in sp}
        return frozenset(j for j in range(m) if vectors[j] in sp)
    flats = {span_members(S) for k in range(rank(range(m)) + 1) for S in itertools.combinations(range(m), k)}
    flats = sorted(flats, key=lambda F: (len(F), sorted(F)))
    return lattice_from_flats(flats, [rank(sorted(F)) for F in flats])

# ---------- incidence algebra ----------
def build(lat):
    n, le, rho = lat
    pairs = [(s, t) for s in range(n) for t in range(n) if le[s][t]]
    ival = {(s, t): [w for w in range(n) if le[s][w] and le[w][t]] for (s, t) in pairs}
    return n, le, rho, pairs, ival

def conv(A, a, b):
    n, le, rho, pairs, ival = A
    return {(s, t): (lambda acc: acc)(sum_polys([pmul(a[(s, w)], b[(w, t)]) for w in ival[(s, t)]])) for (s, t) in pairs}
def sum_polys(L):
    out = []
    for p in L: out = padd(out, p)
    return out

def inverse(A, a):
    """two-sided inverse of an incidence function with a_ss = +-1 (left inverse via recursion)."""
    n, le, rho, pairs, ival = A
    order = sorted(pairs, key=lambda st: rho[st[1]] - rho[st[0]])
    inv = {}
    for (s, t) in order:
        d = a[(t, t)]; assert d in ([1], [-1])
        if s == t: inv[(s, t)] = d[:]          # 1/(+-1) = +-1
        else:
            acc = sum_polys([pmul(inv[(s, w)], a[(w, t)]) for w in ival[(s, t)] if w != t])
            inv[(s, t)] = pneg(pmul(acc, d))   # b_st = -(sum_{w<t} b_sw a_wt) / a_tt
    return inv

def cfh(lat):
    A = build(lat); n, le, rho, pairs, ival = A
    zeta = {p: [1] for p in pairs}
    mu = inverse(A, zeta)
    R = lambda st: rho[st[1]] - rho[st[0]]
    chi = {(s, t): sum_polys([pmul(mu[(s, w)], [0] * (rho[t] - rho[w]) + [1]) for w in ival[(s, t)]]) for (s, t) in pairs}
    kappa = {p: sc((-1) ** R(p), rev(chi[p], R(p))) for p in pairs}
    kbar = {p: ([-1] if p[0] == p[1] else div_x_minus_1(kappa[p])) for p in pairs}
    Hs = {p: pneg(v) for p, v in inverse(A, kbar).items()}
    # check H* is a two-sided inverse statement: H* kbar = -delta
    chk = conv(A, Hs, kbar)
    assert all(chk[p] == ([-1] if p[0] == p[1] else []) for p in pairs)
    # right KLS: f = mu^sgn ; check kappa f = f^rev, f_ss=1, 2 deg f_st < rho_st
    f = {p: sc((-1) ** R(p), mu[p]) for p in pairs}
    frev = {p: rev(f[p], R(p)) for p in pairs}
    kf = conv(A, kappa, f)
    assert all(kf[p] == frev[p] for p in pairs), 'mu^sgn is not the right KLS function'
    assert all(f[(s, s)] == [1] for s in range(n))
    assert all(2 * (len(f[p]) - 1) < R(p) for p in pairs if p[0] != p[1] and f[p])
    Fs = conv(A, Hs, frev)
    bot = min(range(n), key=lambda i: rho[i]); top = max(range(n), key=lambda i: rho[i])
    return Hs[(bot, top)], Fs[(bot, top)], A, bot, top

# ---------- flag numbers, Lean chain formula, Thm 4.9 ----------
def alphas(A, bot, top):
    n, le, rho, pairs, ival = A; r = rho[top]
    al = {}
    for k in range(r):
        for S in itertools.combinations(range(1, r), k):
            # count chains bot < c1 < ... < ck < top with ranks S
            cnt = 0
            def rec(prev, i):
                nonlocal cnt
                if i == len(S): cnt += 1; return
                for w in range(n):
                    if rho[w] == S[i] and le[prev][w]: rec(w, i + 1)
            rec(bot, 0); al[S] = cnt
    return al

def augF(g): return sc(-(-1) ** g, geom(g + 1))
def augW(top, S):           # S descending
    if not S: return augF(top)
    return pmul(augF(top - S[0]), augW(S[0], S[1:]))
def chowW(top, S):
    if not S: return sc(-(-1) ** top, geom(top))
    return pmul(sc(-(-1) ** (top - S[0]), geom(top - S[0])), augW(S[0], S[1:]))

def lean_chain(al, r):
    H = sum_polys([sc(al[S], chowW(r, tuple(sorted(S, reverse=True)))) for S in al])
    F = sum_polys([sc(al[S], augW(r, tuple(sorted(S, reverse=True)))) for S in al])
    return H, F

def thm49(al, r):
    R = tuple(range(1, r))
    beta = {S: sum((-1) ** (len(S) - len(T)) * al[T] for k in range(len(S) + 1) for T in itertools.combinations(S, k)) for S in al}
    H = []; F = []
    for k in range(len(R) + 1):
        for S in itertools.combinations(R, k):
            if any(b - a == 1 for a, b in zip(S, S[1:])): continue
            Sc = tuple(i for i in R if i not in S)
            term = lambda e: pmul([0] * len(S) + [1], pow_poly([1, 1], e))
            F = padd(F, sc(beta[Sc], term(r - 2 * len(S))))
            if (r - 1) not in S: H = padd(H, sc(beta[Sc], term(r - 1 - 2 * len(S))))
    return H, F
def pow_poly(p, e):
    out = [1]
    for _ in range(e): out = pmul(out, p)
    return out

# ---------- run ----------
random.seed(11)
cases = [('B3', boolean(3)), ('B4', boolean(4)), ('B5', boolean(5)), ('U(4,6)', uniform(4, 6)), ('U(5,7)', uniform(5, 7))]
pg32 = [v for v in range(1, 16)]
cases.append(('PG(3,2)', binary(pg32)))
for trial in range(6):
    vecs = random.sample(range(1, 32), random.randint(7, 11))
    lat = binary(vecs)
    if max(lat[2]) == 5: cases.append((f'binary rank5 #{trial} ({len(vecs)} pts)', lat))
for trial in range(4):
    vecs = random.sample(range(1, 16), random.randint(6, 12))
    lat = binary(vecs)
    if max(lat[2]) == 4: cases.append((f'binary rank4 #{trial} ({len(vecs)} pts)', lat))
for name, lat in cases:
    H, F, A, bot, top = cfh(lat); r = A[2][top]
    al = alphas(A, bot, top)
    Hc, Fc = lean_chain(al, r); Hg, Fg = thm49(al, r)
    ok = (H == Hc == Hg) and (F == Fc == Fg)
    print(f'{name:28s} rank {r}: kernel H*={H}  chain==kernel: {H==Hc and F==Fc}  thm4.9==kernel: {H==Hg and F==Fg}')
    assert ok, name
print('All kernel-definition checks agree with the Lean chain formula and Theorem 4.9.')
