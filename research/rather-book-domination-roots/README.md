The extension tex_math_single_backslash is not supported for gfm
# Rather’s book domination-root conjecture

Let $B_n$ consist of $n$ four-cycles with a common edge and otherwise disjoint vertices. A set dominates when its closed neighborhood is all of $V(B_n)$; $D_n(x)$ counts dominating sets by their sizes.

**The exact real-root classification.** For every $n\ge1$, zero is a double root. There are no other real roots for $n=1$. For even $n\ge2$, there is one simple root below $-2$ and one simple root in $(-1/2,0)$, and no others. For odd $n\ge3$, there are exactly two nonzero real roots, both simple and in $(-1/2,0)$.

The $n=1$ exception to [Rather’s literal Conjecture 5.4](https://arxiv.org/html/2604.08998v2#S5.Thmtheorem4) was already reported and [documented by trureturing](https://www.trureturing.org/research/rather-2026-book-domination-root-conjecture/). It is not a new disproof. The result below establishes the expected classification at **every** remaining order and is a finite-order real-root answer to part of [Alikhani, Brown and Jahari’s Question 3](https://arxiv.org/pdf/1401.2092#page=12), not a classification of complex roots.

## Polynomial identity

Classify a dominating set by the number of chosen common-edge endpoints. Both endpoints allow arbitrary choices on the pages. Exactly one endpoint requires at least one of the two private vertices on each page. With neither endpoint, at least one private vertex on each page is again required, but the two possibilities that always pick just the same side must be removed. This gives the known identity
\[
D_n(x)=(1+2x)(x^2+2x)^n+x^2(1+x)^{2n}-2x^n.
\]
For $n\ge3$ the coefficient of $x^2$ is 1, and for $n=2$ it is 3. For $n=1$ the formula becomes $x^2((x+2)^2+2)$, settling that case. The coefficients are nonnegative and some are positive, so there is no positive real root.

## Even number of pages

Write $x=-t$ with $t>0$, and divide by the positive factor $t^n$. Set
\[
H(t)=t^{2-n}(1-t)^{2n}.
\]
For $0<t<1/2$, the divided polynomial is $(1-2t)(2-t)^n+H(t)-2$ when $n$ is even. Both positive summands are strictly decreasing with negative derivative, and their sum starts above 2 at the left endpoint and ends below 2 at the right endpoint. There is exactly one root, and it is simple.

For $1/2\le t\le2$, the first term $(1-2t)(2-t)^n$ is nonpositive. The function $H$ is decreasing on $[1/2,1]$ and increasing on $[1,2]$ (on the latter interval use $H=t^2((t-1)^2/t)^n$). Its two endpoint values are $2^{-n-2}$ and $2^{2-n}$, both less than 2. There are no roots here.

For $t>2$ put $s=t-2$ and $b=s+1/t=(t-1)^2/t$. Define
\[
J_n(t)=t^2b^n-(2t-1)s^n.
\]
The divided polynomial is $J_n(t)-2$. For $t>2$, $b>s>0$ and $t^2>2t-1$, so $J_n(t)>0$. Moreover
\[
J'_n(t)=2tb^n-2s^n+n\left((t^2-1)b^{n-1}-(2t-1)s^{n-1}\right)>0,
\]
since $t^2-1>2t-1$ for $t>2$. At $t=2$ we have $J_n(2)=2^{2-n}<2$, and $J_n(t)\ge(t-1)^2s^n$ tends to infinity. This gives one simple root below $-2$.

## Odd number of pages

Assume $n\ge3$ is odd. For $1/2\le t\le2$, the divided polynomial is $-(1-2t)(2-t)^n+H(t)+2\ge2$. For $t>2$ it is $J_n(t)+2>0$. It remains to study $0<t<1/2$, where its sign is the sign of
\[
\frac{H(t)+2}{(1-2t)(2-t)^n}-1.
\]
Set $u=t/(1-t)$, so $0<u<1$. The ratio before subtracting 1 becomes
\[
R_n(u)=\frac{u^{2-n}}{(1-u^2)(2+u)^n}
      +2\frac{1+u}{1-u}\left(\frac{1+u}{2+u}\right)^n.
\]
It is strictly convex with positive second derivative. For the first summand this follows by differentiating the logarithm: it is a sum of positive multiples of $-\log u$, $-\log(1-u)$, $-\log(1+u)$, and $-\log(2+u)$, each strictly convex on the interval. For the second, put $f=(1+u)/(1-u)$ and $v=((1+u)/(2+u))^n$. Here $f,f',f'',v,v'$ are positive and
\[
\frac{v''}{v'}=\frac{n-3-2u}{(1+u)(2+u)}\ge-1,
\qquad
\frac{2f'}{f}=\frac{4}{1-u^2}\ge4.
\]
Therefore $(fv)''=f''v+fv'(2f'/f+v''/v')>0$.

At both endpoints $R_n$ diverges to infinity. It falls below 1 somewhere in between: at $t=1/5$ for $n=3$, the denominator $(1-2t)(2-t)^3$ exceeds $H(t)+2$ by $589/3125$; for all odd $n\ge5$, take $t=1/3$, where the ratio is $(4/5)^n/3+6(3/5)^n<1$. Strict convexity now gives exactly two intersections with level 1, on opposite sides of the sublevel interval. At these intersections the derivatives are respectively negative and positive, so both roots are simple after changing back to $x$.

## Priority and scope

The paper’s polynomial identity and the already published $n=1$ exception are credited above. The even-case existence intervals alone are already in Rather’s Proposition 5.3. The contribution here is exhaustiveness, simplicity, and the two nonzero odd roots in all orders $n\ge3$. Exact title, author, equation, real-root/parity, MathDB and trureturing searches found the prior literal counterexample but no source offering this all-order classification. The result is not counted as a prior-unsolved disproof of Conjecture 5.4, and no complex-root classification is claimed. [Tracking issue #843](https://github.com/1337isnot1337/solved-conjectures/issues/843).
