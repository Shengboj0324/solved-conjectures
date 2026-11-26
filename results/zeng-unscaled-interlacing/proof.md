# Zeng’s unscaled interlacing question

Fix $0<q<1$ and $\theta>-1$, and put $c=q^{\theta+1}$. Write $(a;q)_k=\prod_{j=0}^{k-1}(1-aq^j)$ and $b_k=(q;q)_k(c;q)_k$. Jiang Zeng's original row polynomials are

```math
P_n(t)=\sum_{k=0}^{n}q^{k(k-1)}\frac{b_n}{b_k b_{n-k}}t^k.
\tag{1}
```

Zeng proves strict interlacing after replacing $P_n(t)$ by $P_n(q^{-(n-1)}t)$. His concluding question 1 asks about the unscaled rows (1). [Zeng, version 2, equations (1.3), (9.1)–(9.2), Theorem 9.3 and final question 1](https://arxiv.org/abs/2610.28691v2)

**Theorem.** Write the roots of $P_n$ as $-r_{n,1},\ldots,-r_{n,n}$ in order of increasing positive magnitude. For every $n\ge1$ and $1\le i\le n$,

```math
 r_{n+1,i}<r_{n,i}<q^2r_{n+1,i+1}.
 \tag{2}
```

In particular each zero of the original $P_n$ lies strictly between successive zeros of $P_{n+1}$.

## Dilation and negative zeros

For a polynomial $p$ with positive constant and leading coefficient, call its positive root magnitudes $0<r_1<\cdots<r_d$ strictly $q$-separated when $r_i/q<r_{i+1}$. Weak separation allows equality in this last inequality. Throughout this proof the polynomials in question have exactly the indicated negative roots. Write $(D_h p)(t)=p(ht)$.

If $p$ has strictly $q$-separated roots and $0<a<1$, the $i$th root magnitude of $(I-aD_q)p$ lies in

```math
(r_{i-1}/q,r_i),\qquad r_0=0.
\tag{3}
```

At magnitude $r_i$ its sign is that of $-p(-qr_i)$, namely $(-1)^i$. At magnitude $r_{i-1}/q$ for $i>1$ its sign is that of $p(-r_{i-1}/q)$, namely $(-1)^{i-1}$. At zero the value is positive. The disjoint intervals account for the full degree. In particular the result is strictly $q$-separated.

For $0<a<q^d$, the $i$th root magnitude of $(I-aD_{1/q})p$ lies in

```math
(r_i,qr_{i+1})\quad(i<d),\qquad(r_d,\infty)\quad(i=d).
\tag{4}
```

At $r_i$ the sign is that of $-p(-r_i/q)$, namely $(-1)^{i+1}$. At $qr_{i+1}$ the sign is that of $p(-qr_{i+1})$, namely $(-1)^i$. The leading coefficient is positive, giving the last root. If $a=q^d$, the leading term cancels and the first $d-1$ intervals in (4) already supply the full set of roots. In both cases the resulting roots are strictly $q$-separated and each root shifts to a strictly larger magnitude than the old root at the same index.

We will also need (3) when the initial separation is weak. One can perturb the root magnitudes to strictly separated ones and pass to the limit. The new $i$th root is then in $[r_{i-1}/q,r_i]$. Whenever these two endpoints differ, the same sign calculation gives strict inclusion, including for the first root. Thus the new roots remain weakly separated. The first gap becomes strict, since the first root moves below $r_1$ and the second is at least $r_1/q$. More generally, if the first $h$ gaps were strict, every new root through index $h+1$ is strictly below its old magnitude, while the following new root is at least that old magnitude divided by $q$. The first $\min(h+1,d-1)$ new gaps are therefore strict. At most $d$ successive operators of form (3), with parameters in $(0,1)$, turn weak separation into strict separation.

## Separation of the source polynomials

Let $\left[{n\atop k}\right]_q=(q;q)_n/((q;q)_k(q;q)_{n-k})$ and form

```math
U_n(t)=\sum_{k=0}^n q^{k(k-1)}\left[{n\atop k}\right]_q t^k.
```

The Gaussian Pascal recurrence gives $U_{n+1}(t)=U_n(t)+q^n t U_n(qt)$, with $U_1(t)=1+t$. If $U_n$ has strictly separated root magnitudes $r_1,\ldots,r_n$, the next polynomial has one root magnitude in each of $(0,r_1)$, $(r_{i-1}/q,r_i)$ for $2\le i\le n$, and $(r_n/q,\infty)$. At $r_i$ its value has the sign of $-U_n(-qr_i)$, and at $r_i/q$ it has the sign of $U_n(-r_i/q)$. At infinity its sign at negative arguments is $(-1)^{n+1}$. These intervals prove strict separation by induction.

Now apply to $U_n$ the commuting operators

```math
 (I-cq^j D_q)\,(I-cq^{n+j}D_{1/q}),\qquad j=0,1,2,\ldots .
\tag{5}
```

Each finite factor preserves strict separation by (3)–(4). On the coefficient of $t^k$ the whole product multiplies by

```math
 (cq^k;q)_\infty(cq^{n-k};q)_\infty
 =\frac{(c;q)_\infty^2}{(c;q)_k(c;q)_{n-k}} .
```

All these products converge to positive real numbers. To see that the limiting separation is strict, reserve the $n$ factors $I-cq^jD_q$ with $0\le j<n$, applying all remaining factors first. The limit at this intermediate stage has positive constant and leading coefficients. Its roots are weakly separated by continuity of the ordered negative roots; none can go to zero or infinity since its degree and positive constant persist. Applying the reserved factors gives strict separation by the last paragraph of the preceding section. The final polynomial is $(c;q)_\infty^2P_n/(c;q)_n$. Thus every $P_n$ has strictly $q$-separated negative zeros.

## Adjacent unscaled rows

Multiplying the coefficient of $t^k$ in $P_{n+1}$ by $(1-q^{n+1-k})(1-cq^{n-k})$ cancels its last two denominator factors for $k\le n$ and annihilates the top coefficient. Equivalently,

```math
(I-cq^nD_{1/q})(I-q^{n+1}D_{1/q})P_{n+1}
   =(1-q^{n+1})(1-cq^n)P_n .
\tag{6}
```

Starting with degree $d=n+1$, the first operator on the right of the composition in (6) uses the boundary value $a=q^d$ in (4); the resulting degree is $n$. The next uses $a=cq^n<q^n$. Each surviving ordered root has moved strictly outward at both steps. In particular $r_{n,i}>r_{n+1,i}$.

Finally, exchanging $k$ and $n-k$ in (1) gives $P_n(t)=q^{n(n-1)}t^nP_n(q^{-2(n-1)}/t)$. Consequently $r_{n,i}r_{n,n+1-i}=q^{-2(n-1)}$. Apply the outward inequality at $n+1-i$ and substitute this identity for the two degrees. It gives $q^{-2(n-1)}/r_{n,i}>q^{-2n}/r_{n+1,i+1}$, the other inequality in (2). This proves the asserted interlacing for all the original rows.
