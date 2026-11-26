# Multicolor Steiner triple system sail problem

Granath, Gyárfás, Hardee, Watson and Wu asked whether the sail is Ramsey in every fixed number of block colors in arbitrary large Steiner triple systems. A sail consists of three triples through a center, and one transversal triple that meets each spoke in a point different from the center. The [two-color result](../../results/steiner-triple-system-sail/PROOF.md) answers the binary question. Sárközy's Theorem 1.4 previously forced either a sail in a designated color or a wicket in another. [Original paper](https://users.renyi.hu/~gyarfas/Cikkek/182_jcd1.pdf) · [Sárközy, Problem 1.3](https://real.mtak.hu/162638/1/98.pdf) · [Issue #852](https://github.com/1337isnot1337/solved-conjectures/issues/852).

## A polynomial independence obstruction in every number of colors

Fix $t\ge1$. For a linear triple system $H$ on $m$ vertices write $a$ for its largest set containing no whole triple. If a $t$-coloring of its triples has no monochromatic sail, then
```math
 m\le C_t a^{2-2^{-t}} .
```
For a Steiner triple system on $n$ vertices the stronger bound $n-1\le t C_{t-1}a^{2-2^{-(t-1)}}$ holds. Constants depend only on $t$, and $C_0=1$. Consequently, in every $t$-coloring of a system with $a=n^{1/2+o(1)}$ there is a vertex-disjoint packing of monochromatic sails covering $n-o(n)$ vertices. One color supplies at least $(1/(7t)-o(1))n$ disjoint sails.

**Proof.** Let $F_t(a)$ bound the order of a linear triple system with independence number at most $a$ and a sail-free $t$-coloring. With no colors there are no triples, so $F_0(a)=a$. For a vertex $p$ and color $c$, take the set $N_c(p)$ of neighbors joined to $p$ by some triple of color $c$. There is no color-$c$ triple inside $N_c(p)$. Such a triple would have three distinct spokes through $p$; all their other vertices are distinct and outside the transversal by linearity. It would give a monochromatic sail. The induced system on $N_c(p)$ thus has at most $t-1$ colors and independence number at most $a$. Consequently $|N_c(p)|\le F_{t-1}(a)$. Each color-$c$ triple incident with $p$ contributes two distinct neighbors, so the maximum degree $D$ satisfies $2D\le tF_{t-1}(a)$.

In any triple system of maximum degree $D$, choose vertices independently with probability $1/\sqrt{D+1}$ and remove one vertex from each surviving triple. The expected size remaining is at least
```math
 m(D+1)^{-1/2}-\frac{mD}{3}(D+1)^{-3/2}
 \ge\frac{2m}{3\sqrt{D+1}} .
```
This gives $F_t(a)\le(3/2)a\sqrt{1+t F_{t-1}(a)/2}$ using upper bounds inductively. The exponent starts at one and obeys $e_t=1+e_{t-1}/2$, proving $e_t=2-2^{-t}$. In a full Steiner system $\sum_c|N_c(p)|=n-1$, yielding the stronger bound. Finally take a maximal vertex-disjoint packing. Its uncovered induced system is sail-free in the given coloring and still has independence number at most $a$. Thus at most $C_ta^{2-2^{-t}}$ vertices are uncovered. This is $o(n)$ when $a=n^{1/2+o(1)}$.

Small-independence Steiner systems are known to exist. This argument applies to every system with the indicated independence bound. Arbitrary Steiner systems can have much larger independent sets, so the all-host multicolor question remains open. [Grable, Phelps and Rödl, *The minimum independence number for designs*](https://doi.org/10.1007/BF01200754).

In the uniform random host model there is also a [positive multicolor sail density inside every linear-sized vertex subset](random-systems.md). This holds simultaneously for all block colorings and yields nearly spanning disjoint packings.
