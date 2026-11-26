# Averaging the block-size counts before restriction

The all-order Erdős–Purdy problem admits an equivalent construction target in which individual block sizes may be much more frequent. For a pairwise balanced design $D$ on $v$ points let $m_s$ be its number of blocks of size $s$ and put

```math
W(D)=\max_{j\ge1}\frac{1}{2j+1}\sum_{j^2\le s<(j+1)^2}m_s.
```

**Theorem.** Fix $0<\varepsilon<1/2$. Whenever $\varepsilon v\le n\le(1-\varepsilon)v$, there is a nontrivial $n$-point restriction $D'$ with $\max_s m_s(D')\le C_\varepsilon W(D)$. In particular, the original $O(\sqrt n)$ conjecture is equivalent to finding an unbounded sequence of designs of bounded consecutive order ratio with $W(D)=O(\sqrt v)$.

To see the difference, at block sizes comparable to $\sqrt v$, one window has width comparable to $v^{1/4}$. A single size in it may occur on the order of $v^{3/4}$ times. The conclusion requires that all the blocks in that whole window together number $O(v^{3/4})$. For example, a design with all block sizes between fixed positive multiples of $\sqrt v$ and with at most $O(v^{3/4})$ blocks per window meets the criterion. Existence of such a family is open.

## A probability bound at individual sizes

Use the exact-size experiment and factorial moments of the [restriction theorem](restriction.md), with $p=n/v$ and $h=h_0+\lceil3\log_2(t+2)\rceil$ at output size $t$. Denote by $w_s$ its conditional upper bound for a size-$s$ block. There are constants $C,c>0$ depending only on $\varepsilon,h_0$ such that, for $s\ge t$,

```math
w_s\le \frac{C}{\sqrt{s}}\exp\!\left[-c\left(\sqrt{s}-\sqrt{t/p}\right)^2\right]. \tag{1}
```

For a binomial variable with $l$ trials, uniformly for $\varepsilon\le p\le1-\varepsilon$,

```math
\Pr(\mathrm{Bin}(l,p)=a)\le\frac{C_1}{\sqrt{l+1}}
 \exp\!\left[-c_1(a-pl)^2/(l+1)\right].
```

Indeed, split the trials into two halves of sizes differing by at most one. If their sum is $a$, one half deviates from its mean by at least $|a-pl|/2$. For either choice of deviating half, condition on its count. The other half must take a particular value and has maximal point mass $O_\varepsilon((l+1)^{-1/2})$. Hoeffding’s inequality for the deviating half and the union bound give the estimate. The cases $l=0,1$ follow by increasing $C_1$.

When $s\ge2h$, apply the estimate with $l=s-h$, $a=t-u$ and $0\le u\le h$. The displacement from $t-ps$ is at most $h$ and $h^2/s$ is bounded, since $s\ge t$ and $h=O(1+\log t)$. The inequality $(|z|-h)_+^2\ge z^2/2-h^2$ absorbs this displacement into the constants. Finally,

```math
\frac{(t-ps)^2}{s}=p^2(\sqrt{s}-\sqrt{t/p})^2\frac{(\sqrt{s}+\sqrt{t/p})^2}{s}
\ge \varepsilon^2(\sqrt{s}-\sqrt{t/p})^2.
```

The range $t\le s<2h$ contains only finitely many integer pairs for fixed $h_0$. Increasing $C$ proves (1) there as well. A block smaller than $t$ has weight zero.

## Summing by windows

On $j^2\le s<(j+1)^2$ the prefactor in (1) is at most $C/j$, while the distance in its exponent is at least $(|j-\sqrt{t/p}|-1)_+$. The block count in the window is at most $(2j+1)W(D)$. The translated Gaussian sum on the integers is uniformly bounded, so

```math
\sum_s m_sw_s\le C_2 W(D)
   \sum_{j\ge1}\exp\!\left[-c(|j-\sqrt{t/p}|-1)_+^2\right]
\le C_3 W(D).
```

The pair count and the de Bruijn–Erdős theorem give at least $3v/4$ blocks of size at most $\lceil2\sqrt v\rceil$. The sum of the widths of the windows meeting those sizes is $O(\sqrt v)$, so $W(D)\gg\sqrt v$. This absorbs the $O(\sqrt v)$ blocks larger than $v^{3/4}$ discarded in the original factorial-moment proof. On the remaining blocks its moment bound is now $\mathbb E(X_t)_h\le D_\varepsilon(C_3W(D))^h$. Its tail estimate, union bound in $t$ and retained noncollinear triple give the asserted restriction. The implied constants are independent of the order and design.

A sequence of bounded order ratio with the window bound supplies every sufficiently large order by the order-selection argument in the [restriction theorem](restriction.md). Conversely $W(D)\le\max_s m_s(D)$, so the original conjecture supplies the required sequence. This equivalence leaves the construction problem open.
