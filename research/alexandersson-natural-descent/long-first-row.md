# Alexandersson's natural-descent conjecture

Let $\mu$ be any fixed nonempty Ferrers diagram with $p$ cells. If its natural-descent polynomial $N_\mu$ is real-rooted, then $N_{(m,\mu)}$ has **$p$ simple negative zeros** for every sufficiently large first-row length $m$. Moreover the rows obtained at $m$ and $m+1$ strictly interlace. This gives unbounded families in arbitrarily many rows, starting with any rectangle, and the extension may be applied repeatedly. The threshold can depend on the entire fixed diagram. [Alexandersson's statement and the rectangle theorem](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsPolytopes)

The zeros have explicit leading constants. If $h_d=[t^d]N_\mu(t)$, define
```math
 F_\mu(x)=\sum_{k=0}^p \frac{x^k}{k!}\sum_{d=0}^k h_d\binom{p-d}{k-d}.
```
Writing its zeros as $\xi_1<\cdots<\xi_p<0$, the $i$th zero of $N_{(m,\mu)}$ in increasing order is $\xi_i/m+O_\mu(m^{-2})$. The limit formula $N_{(m,\mu)}(x/m)\to F_\mu(x)$ itself holds for every $\mu$ and does not require any real-rootedness assumption.

## Lattice counts with a long first row

For a diagram $\lambda$, let $A_\lambda(q)$ count the arrays with entries in $\{0,\ldots,q\}$ weakly increasing along rows and columns. The order-polytope identity is $\sum_{q\ge0}A_\lambda(q)t^q=N_\lambda(t)/(1-t)^{|\lambda|+1}$. One can see it by standardizing the weak arrays using the natural row-by-row labeling. For a fixed extension with $d$ descents, the weakly increasing sequence of its $|\lambda|$ entries must increase strictly at each descent, giving $\binom{q+|\lambda|-d}{|\lambda|}$ choices. [Problem formulation](README.md)

Write $l=\mu_1$. For each fixed $q$, $A_{(m,\mu)}(q)$ is a polynomial in $m$ for $m\ge l$, of degree $q$ with leading coefficient $A_\mu(q)/q!$. To see this, fix the weak array on the lower diagram and the admissible first $l$ entries of the top row, whose last value is $v$. The remaining top-row positions have $\binom{m-l+q-v}{q-v}$ choices. Only $v=0$ contributes in degree $q$. In that case the prefix is entirely zero and every lower array is admissible. The formula includes $q=0$.

Put $c_k(m)=[t^k]N_{(m,\mu)}$. This vanishes for $k>p$, since each natural descent starts with an entry outside the first row. For $0\le k\le p$ the order-polytope identity gives
```math
 c_k(m)=\sum_{q=0}^k(-1)^{k-q}\binom{m+p+1}{k-q}A_{(m,\mu)}(q).
```
It is a polynomial in $m$ of degree at most $k$, with coefficient of $m^k$ equal to $\Delta^k A_\mu(0)/k!$, where $\Delta f(q)=f(q+1)-f(q)$. A second application of the order-polytope identity gives $A_\mu(q)=\sum_d h_d\binom{q+p-d}{p}$. Taking $k$ differences at zero gives $\sum_d h_d\binom{p-d}{p-k}$; terms with $d>k$ vanish. This is precisely the coefficient used in $F_\mu$. In fact $N_{(m,\mu)}(x/m)$ is a fixed polynomial in $x$ and $1/m$ with value $F_\mu(x)$ at $1/m=0$. The degree of $F_\mu$ is $p$, since $\sum h_d$ counts all standard tableaux of shape $\mu$.

## Simple zeros after factorial division

The polynomial $B(x)=\sum_d h_d x^d(1+x)^{p-d}$ has all its zeros strictly negative if $N_\mu$ does. Indeed $B=(1+x)^pN_\mu(x/(1+x))$, so each zero $\rho<0$ gives $\rho/(1-\rho)\in(-1,0)$, and the remaining zeros are at $-1$. The constant term of $N_\mu$ is one.

For $s\ge0$ an integer let $T_s(\sum b_kx^k)=\sum b_kx^k/(k+s)!$. For **every** polynomial with positive leading coefficient and strictly negative real zeros, $T_s$ produces only simple strictly negative zeros, even when the input has multiplicities. Prove this simultaneously for all $s$ by induction on degree. For input $(x+\alpha)g$, $\alpha>0$, take $V=T_{s+1}g$. Direct differentiation gives
```math
 T_s((x+\alpha)g)=(x+\alpha(s+1))V+\alpha x V'.
```
At the simple negative zeros of $V$, the signs are those of $-V'$ and alternate. The signs at $-\infty$ and zero give one further root at each outer end. These disjoint intervals exhaust the degree. For constant $V$ the resulting linear polynomial has one negative zero. This proves the induction. By coefficient expansion $F_\mu=T_0 B$, which proves the claimed strictness.

## Consecutive first-row lengths

At $u=1/m=0$, the polynomial in $(u,x)$ from the count has $p$ simple negative zeros. The implicit function theorem gives real analytic branches $x_i(u)=\xi_i+\gamma_i u+O_\mu(u^2)$ for real $u$ near zero. They exhaust the polynomial degree. The original zeros are $t_{m,i}=x_i(1/m)/m$, so
```math
 t_{m+1,i}-t_{m,i}=-\xi_i/m^2+O_\mu(m^{-3})>0,
 \qquad t_{m,i+1}-t_{m+1,i}=(\xi_{i+1}-\xi_i)/m+O_\mu(m^{-2})>0.
```
This proves strict interlacing. The argument gives the full conjectured root property along the long-row extension of any real-rooted tail. It leaves open diagrams in which several comparable row lengths grow together and the general all-shape statement. Brenti's Gaussian-poset theorem covers a rectangular starting diagram. Wagner's product-of-order-polynomials theorem deals with disjoint unions, whereas the top row here has column relations with the original diagram. [Brenti](https://doi.org/10.1090/memo/0413) · [Wagner](https://doi.org/10.1016/S0195-6698%2805%2980036-8)

An [exact arithmetic check](check_long_row.py) compares 45 leading coefficients with forward differences of independently computed determinant numerators. It also isolates 78 simple negative finite-row zeros and checks their strict order in six consecutive-row pairs.
