The extension tex_math_single_backslash is not supported for gfm
# Bollobás–Erdős–Tuza maximal-independent-set conjecture

## The limitation of the recursive construction

The [recursive construction](RECURSIVE.md) for [Erdős #611](https://www.erdosproblems.com/611) yields $c$-hollow graphs on $n$ vertices with transversal size at least
\[
n\exp\{-O_c(\sqrt{\log n\,\log\log n})\}.
\]
The factor is not just an artifact of using quadratic-decay parameters. Within that construction, allowing **arbitrary** row counts and label counts at each stage, the order of the exponent loss is necessary.

Fix the seed graph, and at every stage substitute the preceding graph into each of the $m_j$ labels and the complete multipartite graph with $D_{j-1}$ parts of size 2 into each of the $r_jm_j$ row positions. Assume $1\le r_j<m_j$, and write $L_j,D_j,i_j$ for order, minimum maximal-independent transversal size, and minimum maximal independent set size. Let $\rho_j=D_j/L_j$, $c_j=i_j/L_j$, $a_j=r_j/m_j$, and $b_j=2r_j\rho_{j-1}$. The substitution identities give
\[
L_j=m_jL_{j-1}(1+b_j),\qquad D_j=(r_j+1)D_{j-1}.
\]
If the final graph at level $t$ is $c$-hollow, then
\[
D_t/L_t\le \exp\{-\Omega_c(\sqrt{\log L_t\,\log\log L_t})\}
\]
for large $L_t$, with constants also allowing for the fixed seed.

**Proof.** At a level, using every label but no row positions is itself a maximal independent support. Use a minimum maximal independent set in every selected fiber to obtain
\[
c_j\le c_{j-1}/(1+b_j).
\]
In particular every earlier level is at least $c$-hollow if the last is. Thus $\sum_{j\le t}\log(1+b_j)\le\log(1/c)$ and each $b_j\le1/c-1$, which also bounds $\sum b_j$ in terms of $c$.

There is another maximal support: choose one position in each row using pairwise distinct labels, and then all labels not chosen in the rows. Its lifted minimum-size choice gives
\[
i_j\le 2r_j+(m_j-r_j)i_{j-1}.
\]
When $i_{j-1}\ge4$, the right side is at most $m_ji_{j-1}(1-a_j/2)$. As $L_j$ at least doubles each time, at most $O_c(1)$ early levels fail $i_{j-1}\ge 4$; the bound $c_j\ge c$ handles the rest. Multiplying the inequalities from the remaining levels gives $\sum a_j=O_c(1)$.

The ratio $\rho_j/\rho_{j-1}=(r_j+1)/(m_j(1+b_j))$ is at most 1 and at most $2a_j$. By AM–GM, for some fixed $K$,
\[
\rho_t\le \rho_0\left(\frac Kt\right)^t.
\]
Put $R=\log(1/\rho_t)$. It follows that $t=O_c(R/\log R)$ when $R$ is large. Also $r_j+1\le K'/\rho_{j-1}$ from the bound on $b_j$. Telescoping the exact equation for $D_j$ and using $\rho_{j-1}\ge\rho_t$ yields
\[
\log L_t
=\log D_0+R+\sum_{j=1}^t\log(r_j+1)
\le \log D_0+R+t(R+\log K')
=O_c(R^2/\log R).
\]
For large $L_t$ this first forces $R\gg_c\sqrt{\log L_t}$, hence $\log R\gg\log\log L_t$, and substitution gives the claimed lower bound on $R$.

This is an architecture-specific upper bound, not an upper bound on all $c$-hollow graphs. It rules out reaching linear transversals by better tuning of the present parameter schedules alone. More generally the same bound holds with high fibers of order at least $D_{j-1}$, transversal cost $D_{j-1}$, and uniformly bounded minimum maximal independent set size, provided they are identical within each level. In that variant use $b_j=r_j|H_j|/L_{j-1}$, bound the row contribution by the uniform minimum-size bound in place of 2, and repeat the same estimates. Removing the loss needs a different construction or high fibers whose minimum maximal independent set size grows substantially.
