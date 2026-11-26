# Erdős–Ruzsa conjecture

**Two fixed shifts cannot cover.** Fix real $C>0$ and distinct integers $a,b$. For every sufficiently large $N$, choose any set of primes up to $N$ with reciprocal sum at most $C$. At each selected prime $p$, independently of the choices at the other moduli, choose **either** $a\bmod p$ **or** $b\bmod p$ as its forbidden class. At least $\delta(C,a,b)N$ integers in $[1,N]$ avoid every forbidden class, for some $\delta(C,a,b)>0$. The prime sets and all choices between the shifts may change with $N$.

There is also a constant $\kappa(C)>0$ independent of the pair and of the finite cutoff: for every fixed $B$, every sequence of bounded-cost full covers must have limiting lower reciprocal mass at least $\kappa(C)$ on primes $p>B$ whose classes differ from **both** prescribed residues. Conversely, if the mass of these exceptional primes is at most $\kappa(C)-\eta$ for a fixed $\eta>0$, a positive fraction survives, allowing all primes up to $B$ to use arbitrary classes. The survivor fraction can depend on $B,a,b,\eta$. This includes arbitrary residues on any fixed collection of primes with convergent reciprocal sum. The original question allows unrestricted residues at all primes and remains open. [Erdős–Ruzsa, p. 386](https://www.sciencedirect.com/science/article/pii/0022314X80900323) · [Erdős problem 1200](https://www.erdosproblems.com/1200)

The two residues may also be translated together by a common center chosen **anywhere in the tested interval**, with fixed separation. Indeed one side of the center contains an interval of length at least $(N-1)/2$. Measured from the center and, if needed, reflected, that interval starts at one and the two shifts have separation $h$ or $-h$. Primes larger than its length plus $|h|$ have no effect except at the finitely many zero arguments, which may be discarded. Among the primes between the length and the length plus $|h|$, each removes only $O_h(1)$ points. The fixed-shift conclusion therefore gives a positive proportion uniformly in the center.

## The two theorems used

For a finite set $D$ of primes, write $g_D(n)=1$ if no prime of $D$ divides $n$, and zero otherwise. This is a real completely multiplicative function. The zero-class small sieve of Erdős and Ruzsa gives $\sum_{n\le X}g_D(n)\ge c_0(C)X$ for large $X$, uniformly for $\sum_{p\in D}1/p\le C$. Primes greater than $X$ have no effect. It follows that the dyadic mean
```math
 M_X(g_D)=X^{-1}\sum_{X\le n\le2X}g_D(n)\ge c(C)>0
```
uniformly. Indeed, Teräväinen's Lemma 2.2 gives $M_{X/2^j}(g_D)=M_X(g_D)+o(1)$ for every fixed $j$, uniformly in $D$. Choose a fixed $J$ with $2^{-J}<c_0(C)/4$, split the range $[X/2^J,X]$ into dyadic intervals, and apply the prefix lower bound. We use $c(C)$ for the resulting positive constant. [Erdős–Ruzsa, Theorem 1](https://www.sciencedirect.com/science/article/pii/0022314X80900323) · [Teräväinen, Lemma 2.2](https://arxiv.org/abs/1710.01195)

We also use Teräväinen's binary correlation theorem for bounded real multiplicative functions. For fixed nonzero $h$ write
```math
 L_X(f)=\frac1{\log\omega(X)}\sum_{X/\omega(X)\le n\le X}\frac{f(n)}n,
 \qquad 1<\omega(X)\le\log(3X),\quad \omega(X)\to\infty.
```
If $g_1,g_2$ are such functions bounded by one, and $g_1$ is equidistributed on $[X,2X]$ in every residue class of every fixed modulus with normalized error $o(1)$, then along the sequence on which this holds,
```math
 L_X\big(g_1(n)g_2(n+h)\big)=M_X(g_1)M_X(g_2)+o(1).
```
Both functions may depend on $X$. This sequential form follows by fixing the accuracy parameter in Theorem 1.4, checking its finitely many moduli, letting $X$ tend to infinity, and then letting the accuracy parameter tend to zero. The freedom to take $\omega$ arbitrarily slowly increasing is essential here and is used for positive lower density in Teräväinen's own applications. [Teräväinen, Definition 1.1, Theorem 1.4 and Theorem 1.11](https://arxiv.org/abs/1710.01195)

## Removing the small-prime bias in the first factor

Translating the interval by the fixed integer $a$ changes the survivor count by $O_{a,b}(1)$, so use the variables $n$ and $n+h$ with $h=a-b$. Split the primes into disjoint sets $P,Q$ which forbid $p\mid n$ and $p\mid n+h$, respectively. If $p\mid h$, the two conditions coincide, and we place such a prime in $Q$. We first prove the theorem without the finite exceptional list.

Suppose no positive uniform lower bound exists. There would be a sequence $X\to\infty$ and choices $P_X,Q_X$ with survivor counts $o(X)$. Pass to a subsequence on which the membership of each fixed prime in the two sets stabilizes. Let $P_*$ be the limiting first set; its reciprocal sum is at most $C$, by taking finite partial sums. Choose a cutoff $B$ such that
```math
 \sum_{p\in P_*,\ p>B}\frac1p<c(C)^2/4.
```
Set $W=\prod_{p\in P_*,\,p\le B}p$, with the empty product equal to one. This fixed integer is coprime to $h$ and to every prime of $Q_X$ for all large $X$. There is a slowly growing $R_X\to\infty$, $R_X\le\sqrt X$, such that $P_X$ and $P_*$ agree up to $R_X$: diagonalize the stabilization on each finite prime interval. Keep only the primes above $R_X$ in the first multiplicative factor, defining $g_1=g_{P_X\cap(R_X,\infty)}$.

This $g_1$ is equidistributed on $[X,2X]$ modulo each fixed $q$. By inclusion–exclusion, $g_1(n)=\sum_{d\mid n}\lambda_d$, where the nonzero $\lambda_d$ have absolute value one and are supported on squarefree products of primes above $R_X$. For large $X$, every such $d$ is coprime to $q$. In one residue class modulo $q$, the count of its multiples in $[X,2X]$ differs by $O(1)$ from $1/q$ times the unrestricted count. The number of possible $d\le2X$ is $o(X)$: for every fixed $Y$ all of them eventually avoid all prime factors up to $Y$. The upper density of those integers equals $\prod_{p\le Y}(1-1/p)$ by periodicity and tends to zero as $Y\to\infty$. This proves the required equidistribution by summing the discrepancies.

## Recovering the omitted conditions

Let $g_2=g_{Q_X}$. Impose $W\mid n+h$. Every $p\mid W$ then avoids $n$, because $(W,h)=1$. This divisibility constraint can be put in the second factor without requiring a correlation theorem for three functions:
```math
 1_{W\mid m}=\prod_{p\mid W}(1-1_{p\nmid m})
 =\sum_{d\mid W}\mu(d)1_{(d,m)=1}.
```
Each $g_2(m)1_{(d,m)=1}$ is real and completely multiplicative. Apply the binary correlation theorem to each of the fixed number of terms and sum. The resulting main term is
```math
 M_X(g_1)\,M_X(g_2(m)1_{W\mid m})
 =W^{-1} M_X(g_1)M_{X/W}(g_2)\ge c(C)^2/W.
```
The equality uses $g_2(W)=1$. Therefore the logarithmic mean of $g_1(n)g_2(n+h)1_{W\mid n+h}$ is at least $c(C)^2/W-o(1)$.

The only missing conditions are $p\nmid n$ for $B<p\le R_X$ in $P_*$. For each, the simultaneous equations $p\mid n$, $W\mid n+h$ select one residue modulo $Wp$. Partial summation of its interval count gives normalized logarithmic mass at most $1/(Wp)+O(\omega(X)/(X\log\omega(X)))$, uniformly in $p$. Summing over at most $\sqrt X$ primes gives a total at most $c(C)^2/(4W)+o(1)$. The factor $1/W$ in this subtraction is needed, since $W$ was selected only after the cutoff for the reciprocal tail. We conclude that the logarithmic mean of actual survivors is bounded below by a positive constant on the subsequence.

Finally choose $\omega(X)$ increasing to infinity sufficiently slowly on the subsequence that $\omega(X)$ times the actual survivor fraction tends to zero, and extend it to a function tending to infinity with $\omega(X)\le\log(3X)$. For instance one can first thin to a subsequence with survivor fraction below $j^{-3}$ and $\log X>j$, then take $\omega(X)=j$ there. Its logarithmic mean of survivors is at most the survivor fraction times $\omega(X)/\log\omega(X)$, a contradiction. This proves the positive uniform lower bound.

## A uniform reciprocal mass must escape the two shifts

One can take $\kappa(C)=c(C)^2$ with the dyadic small-sieve constant above. Suppose along a sequence the survivor count is $o(X)$ and the exceptional primes above a fixed $B_0$ cost at most $c(C)^2-\eta$. Extract local limits as before for all prime decisions, including the actual residue when an exceptional prime is selected. Now choose $B\ge B_0$ large enough that the reciprocal tail of the limiting ordinary first set $P_*$ beyond $B$ is less than $\eta/4$. Take $P_X,Q_X$ to contain the ordinary primes with first and second shifts as before. Include in $W$ the ordinary first primes up to $B$ and all selected exceptional primes up to $B$. The latter have forbidden residues different from the second shift, so $W\mid n+h$ avoids them automatically. Every prime in $W$ lies outside $Q_X$. An exceptional prime may divide $h$; coprimality with $h$ is needed only for the ordinary first primes in $W$, all of which have already been arranged not to divide $h$.

The main correlation contribution is still at least $c(C)^2/W-o(1)$. For every omitted exceptional prime $p>B$, its one forbidden class intersects $W\mid n+h$ in one class modulo $Wp$, regardless of the forbidden residue. The sum of their normalized logarithmic masses is at most
```math
 \frac1W\sum_{p>B,\;p\ \mathrm{exceptional}}\frac1p
 +O\left(\frac{\omega(X)\,\pi(X)}{X\log\omega(X)}\right)
 \le \frac{c(C)^2-\eta}{W}+o(1).
```
Indeed $\pi(X)\ll X/\log X$ and $\omega(X)\le\log(3X)$ with $\log\omega(X)\to\infty$. The missing ordinary first conditions cost at most $\eta/(4W)+o(1)$ by the earlier calculation. A positive logarithmic mean remains, giving the same contradiction. The argument applies for every fixed $B_0$ with the **same** threshold $c(C)^2$. For a fixed exceptional set of finite reciprocal mass, choose $B_0$ large enough to bring its tail below this threshold. This proves all the robustness assertions.

The earlier [common-shift argument](../../docs/erdos-ruzsa-research.md) accommodates a shift growing with $N$ on large primes and arbitrary residues below a fixed power of $N$. This theorem permits the choice between two **fixed** shifts at every prime. Searches under the original small-sieve question, two shifts or residue classes, binary correlations and two consecutive smooth numbers found the one-shift theorem, Hildebrand's sharp zero-class bound, and the correlation results used here. [Hildebrand](https://doi.org/10.4064/aa-48-3-209-260) · [Teräväinen](https://arxiv.org/abs/1710.01195)
