# Erdős’s four-cycle threshold conjecture

**A superlinear edit barrier.** Let $q\ge1024$ be a power of two. On $V=\mathbb F_q^2$ let $G_0$ be the simple affine polarity graph, with distinct $(a,b),(c,d)$ adjacent when $b+d=ac$. If $G$ is $q$-regular and $C_4$-free on $V$, then
$$
|E(G_0)\setminus E(G)| > q^{3/2}/100.
$$
This is independent of the distribution of edits. It strengthens the [first affine-model edit barrier](POLARITY-EDIT-BARRIER.md), but does not exclude candidates far from this model.

## Notation and uniform path count

Write $L_0=\{(0,b):b\in\mathbb F_q\}$. For $w=(c,d)$, write $\ell_w=\{(a,b):b=ca-d\}$. The $\ell_w$ are exactly the nonvertical affine lines, each once. The old neighbors of $w$ are $\ell_w\setminus\{w\}$, so $G_0$ has degree $q-1$ on $L_0$ and $q$ elsewhere. Distinct vertices have at most one old common neighbor, because a nonvertical secant has a unique center $w$. In the model allowing loops, points with unequal first coordinates have that common neighbor; a point has a loop precisely on $L_0$.

Put $D=E(G_0)\setminus E(G)$ and $d_D(w)=|\{e\in D:w\in e\}|$. An added edge $uv$ has at least $q-4$ old simple three-edge paths $u,x,y,v$, with distinct $x$ and distinct $y$. Indeed there are at least $q-1$ choices of $x\in N_{G_0}(u)$. Exclude at most one having first coordinate equal to that of $v$, at most one lying on $L_0$, and at most one adjacent to a looped $v$. The last exclusion uses the fact that distinct lines $\ell_u,\ell_v$ intersect in at most one point. The common neighbor $y$ of $x,v$ in the looped model then differs from $x,v$ by the exclusions and from $u$ because $uv$ is an added edge. Also $x\ne v$ since the edge is added, and two different $x$ cannot give the same $y$ by four-cycle-freeness. This verifies the path count.

## Every sufficiently supported line demands a hub

Call an affine line $L$ **eligible** if at least $q/2$ of its vertices have an added neighbor. Let $R$ be all such vertices on an eligible $L$, and choose one added neighbor $v_u$ for each $u\in R$. If $L$ is nonvertical, delete from consideration all paths whose internal positions include its center $c$, where $\ell_c=L$. At most two paths are lost for each root, by the distinctness of $x$ and $y$. There is no center to exclude when $L$ is vertical.

Every surviving three-edge path must meet $D$, or adding $uv_u$ produces a four-cycle. A deleted first edge can be charged at most twice: each orientation fixes its root $u$, which fixes $v_u$, and the continuation is unique. A deleted middle edge can also be charged at most twice. In orientation $x,y$, there is at most one possible root $u\in L$ adjacent to $x$ in $G_0$, since the old neighborhood line $\ell_x$ meets $L$ in at most one vertex (we excluded its center case). Each root has at most $d_D(v_u)$ last-edge charges, by distinctness of $y$. Hence
$$
|R|(q-6)\le 4|D|+\sum_{u\in R}d_D(v_u).
\tag{1}
$$

Suppose $|D|\le q^{3/2}/100$. For each root that has an added neighbor of deleted degree at most $q/2$, choose such a neighbor. Equation (1) implies that the number of these roots is at most $8|D|/q+12$. All other roots must have chosen neighbors in the heavy set $H=\{w:d_D(w)>q/2\}$, of size at most $4|D|/q$. Partition the latter roots into groups $A_h=\{u:v_u=h\}$, $h\in H$. Discarding groups of size below two leaves at least
$$
q/2-12|D|/q-12\ge q/3
\tag{2}
$$
assigned roots, for $q\ge1024$.

For $h\in H$ let $X_h=N_G(h)\setminus L$ and $z_h=|X_h|$. For $u\in A_h$, consider the distinct secants from $u$ to $X_h$, and let their number be $b_u$. For any distinct $u,u'\in A_h$, a line through $u$ and a line through $u'$ in these families intersect in at most one point and together must account for each point of $X_h$. (The two lines cannot be equal, since a secant here leaves $L$.) Thus $b_u b_{u'}\ge z_h$. Summing $b_u+b_{u'}\ge 2\sqrt{z_h}$ over pairs gives
$$
\sum_{u\in A_h} b_u\ge |A_h|\sqrt{z_h}\qquad (|A_h|\ge2).
\tag{3}
$$

All counted secants are distinct across roots and groups, because each meets $L$ in precisely its root, and each root was assigned only once. At most $q$ are vertical (one per root). At most $q$ nonvertical ones have center equal to their root $u$, since then $u$ is looped and the line is $\ell_u$. At most $q$ have center equal to their other endpoint $x$ from $X_h$, since then $x$ is looped and their line is $\ell_x$. At most $|H|$ have center equal to their hub $h$. For any remaining line with center $w$ and an endpoint pair $u,x$, the proposed graph has common neighbor $h$ for $u,x$. Therefore at least one old edge $uw,xw$ must be deleted, since $w$ is another common neighbor otherwise. Charge that deletion to the line. A deleted edge is charged at most twice, once when each of its endpoints is the center of the charged line. It follows from (3) that
$$
\sum_{h:|A_h|\ge2} |A_h|\sqrt{z_h}\le 2|D|+3q+|H|.
\tag{4}
$$
If all the terms had $z_h\ge q/4$, (2) would make the left side at least $q^{3/2}/6$. But the right side is at most $q^{3/2}/50+3q+\sqrt q/25<q^{3/2}/6$ at $q\ge1024$. We conclude that **every eligible line has a hub** $h$ with more than $3q/4$ neighbors on $L$.

## A finite injection that misses the loop line

A hub working for $L$ is unique: two hubs with more than $3q/4$ neighbors on the same $q$-point line would have two common neighbors. Similarly, a single hub cannot work for two different lines, because the lines meet in at most one point while its total degree is $q$.

The hub obtained above had some assigned root $u$ on $L$ for which $uh$ is an added edge. Therefore $\ell_h\ne L$: every point of $\ell_h$ distinct from $h$ was already adjacent to $h$. Of the old neighbors of $h$, fewer than $q/4$ can still be its neighbors outside $L$, and at most one remains on $L$ since $\ell_h\ne L$. At least $3q/4-2\ge q/2$ vertices on $\ell_h$ therefore lost the old edge to $h$. Each had to gain an added edge, since its degree cannot drop. Thus $\ell_h$ itself is eligible.

We have defined a self-map of the finite set of eligible lines by $L\mapsto\ell_h$. It is injective: distinct lines have distinct hubs and the affine line labels are distinct. Its image consists exclusively of nonvertical lines. But $L_0$ is eligible since every vertex on it had degree $q-1$ originally and must gain an edge. This contradicts injectivity on a finite set. Thus the assumed bound on $|D|$ fails.

## Scope

The theorem applies to every labeling of a hypothetical A-REG candidate. It establishes separation from a specific dense algebraic construction, not a complete classification of asymptotically dense $C_4$-free graphs. No solution of [Erdős #85](https://www.erdosproblems.com/85) is claimed.

## Transfer to arbitrary even orthogonal polarities

The proof only uses affine incidence and the symmetric line labels, so it also applies to the affine truncation of an **arbitrary** orthogonal polarity of an even-order projective plane (including non-Desarguesian planes), when the deleted line at infinity is the polar of an absolute point $p$.

For completeness, the $q+1$ absolute points are collinear in this situation. Every line contains an absolute point: a nonabsolute point $w$ has the involution $x\mapsto x^\perp\cap w^\perp$ on its polar line of odd size $q+1$, with absolute fixed points; the polar line of an absolute point contains that point. Since there are exactly $q+1$ absolute points by orthogonality, a line containing two of them cannot have any point $y$ outside their set: the other $q$ lines through $y$ would need distinct absolute points outside the line, but only $q-1$ remain. Thus the absolute points form one line. It is not the polar $\ell_\infty=p^\perp$: otherwise any other absolute point $p'$ on it would have its own polar containing both $p,p'$ and hence equal to $\ell_\infty$, contradicting injectivity.

Delete all points of $\ell_\infty$. Its pole is $p\in\ell_\infty$, and for the other infinity points their polar lines are exactly the other lines through $p$. Hence the $q^2$ affine points label precisely the affine lines outside the omitted parallel class (the direction corresponding to $p$). Point-line adjacency is symmetric by polarity, and the affine absolute points are exactly the $q$ points of the absolute line, in that omitted class. These are exactly the properties used throughout the proof. Consequently an $o(q^{3/2})$ deletion-distance stability theorem to **any such truncation** would imply the nonexistence of the regular candidates for large even $q$; the present note does not prove that stability hypothesis.
