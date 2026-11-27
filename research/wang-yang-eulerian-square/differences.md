# Wang–Yang’s Eulerian square conjecture

Write $E(a,b)$ for the Eulerian number with $a$ ascents and $b$ descents. Two further properties hold throughout the symmetric extension $a,b\ge0$: mixed forward differences of all orders are nonnegative, and every three-by-three minor containing both the constant row and the constant column is strictly positive. The constant column occurs in Wang and Yang’s square, while the constant row is the additional row $a=0$. The [unrestricted conjecture](README.md) remains open.

## Mixed differences at all origins

Let $\Delta_a,\Delta_b$ denote unit forward differences and set $H_{ij}=\Delta_a^i\Delta_b^j E(0,0)$. The Eulerian recurrence is

$$E(a+1,b+1)=(b+2)E(a,b+1)+(a+2)E(a+1,b).$$

Consequently

$$\Delta_a\Delta_b E=(a+b+3)E+(a+1)\Delta_a E+(b+1)\Delta_b E.$$

For a one-variable sequence $f$, $\Delta^i(af)(0)=i(\Delta^{i-1}f(0)+\Delta^if(0))$, by the discrete product rule. Applying the two coordinate differences to the last display gives

$$H_{i+1,j+1}=(i+1)H_{i+1,j}+(j+1)H_{i,j+1}+(2i+2j+3)H_{ij}+iH_{i-1,j}+jH_{i,j-1}.$$

Terms with negative indices are omitted. The axis values are zero apart from $H_{00}=1$, since $E(a,0)=E(0,b)=1$. Induction gives $H_{ij}>0$ for $i,j\ge1$. Since a shift is $1+\Delta$, at any origin we have

$$\Delta_a^i\Delta_b^j E(a,b)=\sum_{u=0}^a\sum_{v=0}^b{a\choose u}{b\choose v}H_{i+u,j+v}\ge0.$$

Every difference with $i,j\ge1$ is strict. The assertion extends to arbitrary positive integer step lengths in the differences, since a forward difference of step $d$ is a sum of $d$ translated unit differences.

## Three-by-three minors with both constant margins

Subtract the constant row from the other two rows of the minor. Its determinant becomes a two-by-two minor of $E(a,b)-1$ with $a,b\ge1$. The [normalized cardinal-spline inequality](README.md#arbitrary-row-and-column-pairs) implies, for any neighboring square with entries $A,B$ in the first row and $C,D$ in the second, that

$$AD/(BC)\ge(a+b+3)/(a+b+2),\qquad AD-BC\ge AD/(a+b+3).$$

For $a,b\ge1$ one has $A\ge a+b+3$ except at $(1,1)$. Indeed $E(1,2)=11$ and the symmetry gives $E(2,1)=11$. The recurrence shows that each step in a positive coordinate increases an interior entry by at least one. It follows that $AD-BC\ge D$ outside the exceptional square. Hence

$$(A-1)(D-1)-(B-1)(C-1)=AD-BC-D+(B+C-A)>0.$$

At $(1,1)$, the four entries of $E$ are $4,11,11,66$ and the reduced determinant is $95$. Multiplying adjacent row ratios, then adjacent column ratios, extends strict positivity to any two increasing pairs of positive indices. This proves the three-by-three assertion.
