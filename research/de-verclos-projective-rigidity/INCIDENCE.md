# Incidence and propagation at the conjectured dimension threshold

Keep the orientation correspondence $`R`$ and Borel selector $`f`$ of the [secant argument](SECANTS.md). The following two facts work at Hausdorff dimension strictly greater than one, including on planar sets of zero area. They allow the local projectivity step to be studied separately.

## Points approached from both sides of every line

For every planar set $`K`$, the set of $`q\in K`$ for which some line through $`q`$ has an empty open half-disc of $`K`$ about $`q`$ is contained in a countable union of sets of Hausdorff dimension at most one. Indeed choose a rational open ball $`U`$ containing $`q`$ and lying inside the disc of emptiness. Then $`q`$ belongs to the boundary of the closed convex hull of $`U\cap K`$. A bounded convex set in the plane has boundary of dimension at most one, including the degenerate cases. There are countably many $`U`$.

If $`f`$ is continuous on $`K`$ and $`q`$ is outside that exceptional set, both sides of every line through $`q`$ contain points of $`K`$ arbitrarily close to $`q`$. Thus for distinct collinear $`q,r,x`$ and any $`(r,w),(x,z)\in R`$ we have $`\det(f(q),w,z)=0`$, by continuity and the two source signs in (1). We call such a $`q`$ an incidence anchor. Any finite Borel measure that gives zero mass to sets of dimension at most one sees almost every point of a Lusin compact set as an anchor. It suffices that the selector is continuous on the compact set; the other two points may be anywhere in the support.

## A projectivity on a set of dimension greater than one determines the whole relation

The strict secant lemma has a second conclusion. For distinct finite $`u,v`$ a set of dimension greater than one also has a secant putting them on the **same** strict side. If every product $`(a-a')(b-b')`$ in the proof of that lemma were nonpositive, $`(a,b)\mapsto a-b`$ would instead be an isometric embedding into the line. Thus either requested strict sign of the product occurs.

Suppose there is a set $`B\subset E`$ of dimension greater than one and an invertible projectivity $`P`$ such that for each $`b\in B`$ some $`(b,y_b)\in R`$ satisfies $`[y_b]=P(b)`$. Take $`(x,z)\in R`$ and suppose $`[z]\ne P(x)`$. Write $`v=P^{-1}([z])`$ in the projective source plane. Choose an affine chart containing both $`x,v`$ and discard its line at infinity from $`B`$. The image of $`B`$ in the chart still has dimension greater than one by local bi-Lipschitz invariance and countable stability. Write $`A`$ for a matrix taking homogeneous coordinates in this chart back to the original source, and $`M`$ for a matrix representing $`P`$ in the original coordinates. Write $`p^*=(p_1,p_2,1)`$ for normalized chart coordinates. The original finite source lift at $`b`$ is $`\alpha_b A b^*`$ and the target lift $`y_b`$ is $`\beta_b M A b^*`$ for nonzero real scalars. By finite partition we may restrict to a set of dimension greater than one on which both scalar signs are constant.

For any two members $`b,c`$ of this set, (1) for their chosen lifts and $`(x,z)`$ reads

```math
\epsilon\,\det(b^*,c^*,x^*)\det(b^*,c^*,v^*)\geq0
```

for a single fixed $`\epsilon\in\{-1,1\}`$. Indeed $`x`$ has a fixed original lift proportional to $`Ax^*`$ and $`z`$ is proportional to $`MAv^*`$, and the signs of the determinants of the two matrices are fixed. The two strict secant conclusions give both signs for the product, a contradiction. Thus $`[z]=P(x)`$ throughout $`R`$ and $`\nu=P_*\mu`$.
