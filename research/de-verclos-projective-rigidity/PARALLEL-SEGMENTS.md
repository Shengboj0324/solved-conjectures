# Rigidity for a zero-area class of supports

**Theorem.** Suppose $`\mu,\nu`$ are line-null planar probabilities with equal finite order-type laws. If the support $`E`$ of $`\mu`$ contains $`I\times C`$, where $`I`$ is a nondegenerate compact interval and $`C`$ is compact of positive Hausdorff dimension, then $`\nu=P_*\mu`$ for an invertible projectivity $`P`$. This includes a segment times the middle-thirds Cantor set. The hypotheses concern the support alone and impose no product structure on the sampling measure.

Use the [orientation correspondence and finite-chart selector](SECANTS.md) and [incidence anchors and propagation](INCIDENCE.md). Choose $`0<s<\dim_H C`$ and a Frostman probability $`\eta`$ on $`C`$ with $`\eta(J)\leq c|J|^s`$ on intervals. The product of length on $`I`$ and $`\eta`$ has a ball bound $`O(r^{1+s})`$, hence vanishes on sets of dimension at most one. Choose a positive-product-measure compact $`K\subset I\times C`$ on which the Borel selector $`f`$ is continuous and finite. Almost all of $`K`$ for this product measure consists of incidence anchors. Fubini gives a positive-$`\eta`$ set of levels $`t\in\operatorname{supp}\eta`$ on which the finite anchors occupy a positive-length subset of the interior of $`I`$.

On each such row, all projective selector images lie in a line: use one anchor on the row in the incidence lemma and any second point with distinct projective image. Each projective image has at most two preimages because the selector is injective on the hemisphere. The preimage of each fixed target line has dimension at most one and consequently zero product measure. We can therefore choose four different good rows with pairwise different target lines. On each chosen row, finitely many forbidden projective image points exclude only finitely many source points.

## The four image lines are concurrent

Designate any of the four levels $`t_p`$ as pivot. Pick a length-density point $`x_0`$ of its anchor set in the interior of $`I`$. On the other three rows $`t_i`$ choose points $`p_i=(x_i,t_i)`$ near $`(x_0,t_i)`$ such that each joining line $`p_i p_j`$ meets the pivot row in an anchor, and the three anchors are distinct. Here is an explicit justification. Sample $`x_i`$ independently uniformly on $`[x_0-\epsilon,x_0+\epsilon]`$. The abscissa of that intersection is

```math
u_{ij}=\frac{(t_j-t_p)x_i+(t_p-t_i)x_j}{t_j-t_i}.
```

Each $`u_{ij}`$ is within $`O(\epsilon)`$ of $`x_0`$ and has density $`O(1/\epsilon)`$, with constants depending only on the fixed levels. The probability of missing the anchors tends to zero for each pair. Collinearity of the three sampled points has probability zero. We can also discard the finitely many abscissae on each row whose images lie at intersections of the four target lines or at the original target infinity on the row (if the entire row image is the equator, choose another row, which costs zero product measure).

Move the triangle by the shear $`(x,y)\mapsto(x+h(y-t_p),y)`$, with sufficiently small $`h\ne0`$. The resulting $`p'_i`$ remain on their original segments and avoid the same finite exceptional image points as well as projective coincidences with $`f(p_i)`$. The shear fixes the pivot point $`u_{ij}`$, so $`p_i p_j`$ and $`p'_i p'_j`$ pass through that same anchor. Write $`P_i=[f(p_i)]`$, $`P'_i=[f(p'_i)]`$. The target sides $`P_iP_j`$ and $`P'_iP'_j`$ meet at the anchor image by incidence. These sides are distinct: if they coincided, they would contain $`P_i,P'_i`$ and therefore equal the $`i`$th row line, although $`P_j`$ avoids that line. The triangles are nondegenerate: otherwise their common side line would contain the three distinct anchor images and coincide with the pivot line, which their vertices avoid. The three intersections of corresponding sides are collinear on the pivot line. By the converse of Desargues’s theorem, the three target row lines $`P_iP'_i`$ are concurrent. Applying this with two different pivots shows that **all four** target lines pass through the same point, since the two common row lines have a unique intersection.

## Translations on two complete segments

Send the pivot row to infinity in both projective planes. The other source row lines become parallel because they already met at the horizontal point at infinity on that pivot row. Their distinct target lines become parallel by the concurrency just proved. Take affine coordinates in each chart making two of the respective rows $`y=0,1`$. The projective point shared by all rows is the horizontal direction. Apart from that one direction, each pivot point in either chart specifies a vector $`(h,1)`$ up to scale. The map from the original pivot abscissa to $`h`$ is a one-dimensional projectivity and a local diffeomorphism away from its pole.

Choose a density anchor on the original pivot segment so that the vertical line through it meets both original segment interiors at points with finite images in the new chart. Only finitely many original abscissae must be avoided, including the preimages of the target common point. Its image direction is transverse to the two target rows. In the new source chart this transversal has direction $`(h_*,1)`$ and meets the rows at $`(u_*,0),(u_*+h_*,1)`$. There are open intervals about these abscissae consisting entirely of source segment points with finite selected images. Indeed on either row the new target infinity can have at most two source preimages. In these intervals write the maps as $`(x,0)\mapsto(F_0(x),0)`$ and $`(v,1)\mapsto(F_1(v),1)`$, with $`F_i`$ Borel. Choose a fixed interval $`J`$ about $`u_*`$ and a positive-length measurable set $`H`$ of pivot anchor parameters sufficiently close to $`h_*`$ that all $`x\in J`$ and $`x+h`$, $`h\in H`$, belong to these two intervals. Remove the at most two anchor preimages of the target horizontal direction. Incidence at each of the remaining pivot anchors yields

```math
 F_1(x+h)-F_0(x)=d(h)\qquad(x\in J,\ h\in H),
```

where $`(d(h),1)`$ is the target direction. Steinhaus’s theorem gives $`(-\delta,\delta)\subset H-H`$. For $`a=h-k`$ in this interval and $`x,x+a\in J`$, two applications give

```math
F_0(x+a)-F_0(x)=d(h)-d(k).
```

For small $`a`$ this is independent of the representation since the left side can be evaluated at a fixed interior point. The common increment is Borel and locally additive by telescoping inside $`J`$. The measurable Cauchy equation makes it $`ma`$ for a constant $`m`$ (measurability gives boundedness on a positive-length set, then boundedness near zero by Steinhaus, then continuity by subdivision). On a nonempty open subinterval $`J'`$ of $`J`$, $`F_0(x)=mx+b_0`$. The finite-coordinate map is injective there, so $`m\ne0`$.

Choose a density point $`h_0\in H`$ belonging to $`H`$. The translation identity gives $`F_1(v)=mv+b_1`$ on $`J'+h_0`$. For every $`h\in H`$ sufficiently near $`h_0`$, these intervals allow a pair $`x,x+h`$ with the two affine formulas, so $`d(h)=mh+b_1-b_0`$. The affine projectivity

```math
Q(x,y)=(mx+b_0+(b_1-b_0)y,y)
```

therefore agrees with the selector on $`J'\times\{0\}`$ and on at least two different pivot anchor directions transverse to that row.

In a small open neighborhood of any interior point of $`J'\times\{0\}`$, lines from those two directions meet $`J'\times\{0\}`$ inside the interval. At a point off the row, incidence at the two pivot anchors forces every target representative to lie on the two corresponding image lines and hence equal $`Q`$ projectively. On the row the selected representatives already agree. Undo the chart changes. This gives agreement on $`E`$ over an original open neighborhood of an interior point of a full segment at a level in $`\operatorname{supp}\eta`$. Its intersection with $`I\times C`$ has positive product measure and therefore Hausdorff dimension at least $`1+s`$. [Propagation by strict secants](INCIDENCE.md) gives the asserted global projectivity.
