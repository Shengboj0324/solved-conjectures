# Erdős’s four-cycle threshold conjecture

**Edit barrier for the affine polarity graph.** For an even prime power $q\ge8$, put $V=\mathbb F_q^2$ and form the simple graph $G_0$ by taking distinct $(a,b),(c,d)$ adjacent exactly if $b+d=ac$. If a $q$-regular $C_4$-free graph $G$ on $V$ exists, then the graph of changed edges $E(G)\triangle E(G_0)$ has vertex-cover number at least $q/4$. Moreover, writing $D=E(G_0)\setminus E(G)$, one has
$$
q(q-2)\le 3|D|+\sum_{u\in L_0} d_D(v_u)
$$
for every selection of an added neighbor $v_u$ of each $u$ on the affine loop line $L_0$. In particular, an edit with $o(q^2)$ deletions requires that all new neighbors of all but $o(q)$ loop-line vertices lie in a common set of size $o(q)$ of heavily edited vertices. Neither conclusion rules out a global construction.

## The affine line description

The line $\ell_w$ associated with $w=(c,d)$ comprises $(a,b)$ with $b=ca-d$. Every nonvertical affine line appears exactly once, since slopes and intercepts determine $w$. In characteristic two the incidence is symmetric, and $w\in\ell_w$ exactly when $c=0$. Such points form the vertical line $L_0$. The neighbors of $w$ in $G_0$ are $\ell_w\setminus\{w\}$, so the degree is $q-1$ on $L_0$ and $q$ elsewhere. Two vertices with unequal first coordinate have exactly one nonvertical joining line, therefore one common neighbor in the version allowing loops. With the loops removed, that neighbor is still common unless it equals one of the two vertices. Points with equal first coordinate have no common neighbor.

## The vertex-cover obstruction

Assume a set $H$ of $h<q/4$ vertices covers every changed edge and put $U=V\setminus H$. Thus the two graphs agree inside $U$. For any $z\in H$, put $P=N_G(z)\cap U$. Its size is at least $q-h+1$. If two points $x,y\in P$ lie on a nonvertical line $\ell_w$ with $w\in U\setminus\{x,y\}$, then $w$ and $z$ are two common neighbors in $G$, a contradiction. Thus every nonvertical secant through two nonloop points of $P$ has its center in $H$.

If $P$ contains only loop-line points, it is collinear. If $P$ has a nonloop point $x$, the nonvertical lines from $x$ to points of $P\cap L_0$ are distinct. At most one has its center equal to an endpoint: $x$ is not on its own line, and among loop-line points exactly one is adjacent to $x$ in $G_0$. Hence $|P\cap L_0|\le h+1$. The set $P'$ of nonloop points of $P$ has at least $q-2h$ points.

A noncollinear set of $m$ points determines at least $m$ secant lines. Indeed its point–secant incidence matrix $C$ satisfies $CC^{\mathsf T}=J+\operatorname{diag}(r_i-1)$, where $r_i$ is the number of secants through the $i$th point. Each $r_i\ge2$ for a noncollinear set, giving full row rank. At most $m/2$ of its secants are vertical, since distinct vertical secants are disjoint and each contains two points. Thus if $P'$ were noncollinear, more than $h$ nonvertical secants would need centers in $H$, from $q>4h$. So $P'$ is collinear. Any point of $P$ outside its line is a loop-line point and gives $|P'|$ distinct secants to $P'$. At most one is vertical and at most one has its center equal to an endpoint. All others need centers in $H$, impossible since $q-2h>h+2$ for $q\ge8$ and $h<q/4$. This proves that $P$ lies on an affine line, denoted $L_z$.

The lines $L_z$ are distinct for distinct $z\in H$: equal lines would give at least $q-2h+2>1$ common neighbors. Also $L_z$ cannot equal $\ell_w$ for $w\in U$, because at least $q-h$ points of $P$ are still adjacent to $w$ inside $U$, again yielding two common neighbors. Therefore the $h$ chosen lines consist of some of the old lines $\ell_w$ with $w\in H$ and, say, $r$ vertical lines. Exactly $r$ old hub lines are retired.

For every $x\in U$, the required number of neighbors in $H$ is its old number of neighbors in $H$ plus $1_{x\in L_0}$, since the edges inside $U$ are unchanged. Each new hub neighbor needs its selected line to pass through $x$, so a necessary condition is
$$
1_{\{x\text{ lies on a chosen vertical line}\}}
\ \ge\ \#\{\text{retired old hub lines containing }x\}+1_{x\in L_0}.
$$
Any retired line is nonvertical and has at least $q-h$ points in $U$. It meets the $r$ chosen verticals in at most $r\le h<q-h$ points, contradicting the necessary condition. Hence $r=0$. But then the same condition fails on every point of $L_0\setminus H$. This contradiction proves the claimed vertex-cover lower bound.

## A deletion count when changes need not share a vertex cover

Each $u\in L_0$ has at least one added neighbor $v_u$, since its new degree exceeds its old one. Fix any such choice. In the old graph there are at least $q-2$ simple three-edge paths $u,x,y,v_u$ for this pair. To see this, use $x\in N_{G_0}(u)$, excluding at most one $x$ with the same first coordinate as $v_u$. Then the common neighbor $y$ of $x,v_u$ in the looped graph exists. It is not $x$, which is outside $L_0$. It cannot be $v_u$ either: if $v_u$ has a loop it is not adjacent to $x$, since $x$ has unique old neighbor $u$ on $L_0$. Nor is $y=u$ because $uv_u$ is new. The distinct paths have distinct $x$ and distinct $y$, the latter by four-cycle-freeness of $G_0$.

Every such path must contain an old deleted edge, or it closes with $uv_u$ to a four-cycle. A deleted first edge is charged at most once over all selected roots: it fixes its loop-line endpoint $u$, its endpoint $x$, and then $v_u$ and the common neighbor are fixed. A deleted middle edge is charged at most twice: for each orientation $x,y$ there is at most one old loop-line neighbor $u$ of $x$. A last-edge charge contributes at most $d_D(v_u)$ for each root, by distinctness of $y$. These three bounds prove the displayed count.

In particular if every deleted degree is at most $q/2$, then $|D|\ge q^2/6-2q/3$. For the asymptotic alternative, let $r$ be the number of $u\in L_0$ having at least one added neighbor of deleted degree at most $q/2$. Choose such a neighbor for these roots. At the other roots the deleted degree is at most $q$, so the count gives $3|D|\ge rq/2-2q$. If $|D|=o(q^2)$ then $r=o(q)$, while at most $4|D|/q=o(q)$ vertices have deleted degree above $q/2$. All added neighbors of the other $q-o(q)$ roots belong to those heavy vertices, as claimed.

## Scope

This only constrains repairing a specific natural affine model. It says neither that an A-REG candidate must resemble that model nor that such candidates are impossible. The exact [Erdős problem](https://www.erdosproblems.com/85) and the [A-REG route](https://aixiv.online/abs/2610.02192) remain open in this note.
