#!/usr/bin/env python3
"""Vectorised exact flag numbers for point sets S in PG(3,q), q prime (numpy, integer arithmetic).

A plane meets S in a rank-3 flat iff it contains >= 2 lines with >= 2 points of S.
"""
import numpy as np
from itertools import product
from fractions import Fraction


class PG3:
    def __init__(self, q):
        self.q = q
        pts = []
        for v in product(range(q), repeat=4):
            if any(v) and v[next(i for i in range(4) if v[i])] == 1:
                pts.append(v)
        self.P = np.array(pts, dtype=np.int64)
        self.v = len(pts)
        code = lambda a: ((a[..., 0] * q + a[..., 1]) * q + a[..., 2]) * q + a[..., 3]
        lut = -np.ones(q ** 4, dtype=np.int64); lut[code(self.P)] = np.arange(self.v)
        inv = np.array([0] + [pow(x, q - 2, q) for x in range(1, q)], dtype=np.int64)
        def normalise(V):
            lead = np.where(V[:, 0] != 0, V[:, 0], np.where(V[:, 1] != 0, V[:, 1], np.where(V[:, 2] != 0, V[:, 2], V[:, 3])))
            return lut[code(V * inv[lead][:, None] % q)]
        # lines: 2-dim subspaces in RREF
        lines = []
        for piv in [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]:
            free = [(r, c) for r in range(2) for c in range(4) if c > piv[r] and c not in piv]
            for vals in product(range(q), repeat=len(free)):
                B = np.zeros((2, 4), dtype=np.int64)
                B[0, piv[0]] = B[1, piv[1]] = 1
                for (r, c), x in zip(free, vals): B[r, c] = x
                lines.append(B)
        self.L = len(lines)
        Bs = np.array(lines)                                   # L x 2 x 4
        coeff = np.array([(1, 0)] + [(a, 1) for a in range(q)], dtype=np.int64)  # q+1 points
        V = (coeff[None, :, :, None] * Bs[:, None, :, :]).sum(2) % q            # L x (q+1) x 4
        self.line_pts = normalise(V.reshape(-1, 4)).reshape(self.L, q + 1)
        # planes: dual points h; line in plane iff h.b1 = h.b2 = 0
        H = self.P
        d1 = (Bs[:, 0, :] @ H.T) % q == 0; d2 = (Bs[:, 1, :] @ H.T) % q == 0
        lp = np.nonzero(d1 & d2)
        self.line_planes = lp[1].reshape(self.L, q + 1)
        self.plane_pts = np.array([np.nonzero((self.P @ h) % q == 0)[0] for h in H])

    def alpha(self, S):
        S = np.asarray(S, dtype=bool)
        s = S[self.line_pts].sum(1)
        ok = s >= 2
        f2 = int(ok.sum()); a12 = int(s[ok].sum())
        Lp = np.zeros(self.v, dtype=np.int64); Sp = np.zeros(self.v, dtype=np.int64)
        np.add.at(Lp, self.line_planes[ok].ravel(), 1)
        np.add.at(Sp, self.line_planes[ok].ravel(), np.repeat(s[ok], self.q + 1))
        pp = S[self.plane_pts].sum(1)
        r3 = Lp >= 2
        return {(): 1, (1,): int(S.sum()), (2,): f2, (3,): int(r3.sum()), (1, 2): a12,
                (1, 3): int(pp[r3].sum()), (2, 3): int(Lp[r3].sum()), (1, 2, 3): int(Sp[r3].sum())}

    def spans(self, S):
        S = np.asarray(S, dtype=bool)
        return not (S[self.plane_pts].sum(1) == S.sum()).any()
