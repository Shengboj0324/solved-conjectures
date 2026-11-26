# The three-block construction and its exact circular index

For every integer $`g\ge15`$ and every pair of nonnegative integers satisfying $`3\alpha+5\beta=g-3`$, Lean constructs the graph on $`6g+1`$ labelled vertices. The vertices 6, 7 and 8 have degree $`4g+2`$. Every other vertex has degree $`\Delta=4g+3`$, and the real circular chromatic index equals $`\Delta+2/3`$. [Theorem A and Corollary C](../../lean/Conjectures/CircularThreeBlockTheorems.lean) · [Labelled degree formula](../../lean/Conjectures/CircularThreeBlockDegree.lean) · [Original formulas](PROOF.md).

The proof checks the two base matchings, the cyclic lengths of their edges, and the separation of three consecutive colour classes across all three insertion blocks. For each of the three deficient vertices it exhibits empty colour windows. The total degree then determines the degree of every vertex. Corollary C combines this construction with the nine finite graphs for every degree congruent to 3 modulo 4 from 27 onward. The graph is connected for every permitted packing. [Matching formulas](../../lean/Conjectures/CircularThreeBlockBase.lean) · [Deficient vertices](../../lean/Conjectures/CircularThreeBlockDeficit.lean) · [Combined verification](../circular-index-upper-half-remaining-deltas/FORMALIZATION.md).

## The nine finite graphs

For each of the nine parameters $6\le g\le14$, Lean constructs the labelled graph on $6g+1$ vertices from the supplied base matchings and three insertion blocks. It proves that the maximum degree is $\Delta=4g+3$ and that

```math
\chi'_c(G)=\Delta+\tfrac23 .
```

The verified degrees run from 27 to 59 in steps of four. The upper bound comes from the colour assigned to each edge. For the lower bound Lean checks every vertex degree, applies the degree-sum formula to count the edges and applies the density lower bound for every real-circle colouring. The two endpoints agree in all nine cases. [Proposition B](../../lean/Conjectures/CircularFiniteIndexTheorems.lean) · [Degree and index argument](../../lean/Conjectures/CircularTableColoring.lean) · [Original certificates](certificates.json) · [Written uniform theorem](PROOF.md).

The [joint verification and reproduction instructions](../circular-index-complete-minus-edges/FORMALIZATION.md) identify the shared receipt, the source-data comparison and the kernel replay command.

## Small forward insertions and cyclic supports

Lean quantifies over every perfect matching of the labelled support sets and every starting colour. For $g=2,3,4$ no forward block exists for any $1\le k<2g$. For $g=5$ a block exists at every starting colour exactly when $k=2$ or $k=8$. In each surviving case the complementary matchings are forced. Among the 62 labelled colours there is no triple with pairwise edge-disjoint blocks. The exclusions concern the forward construction of Section 8. [Exclusion theorems](../../lean/Conjectures/CircularSmallInsertionExclusions.lean) · [Positive matchings](../../lean/Conjectures/CircularSmallInsertionPositive.lean) · [Proof of incompatibility](../../lean/Conjectures/CircularSmallInsertionTranslation.lean).

For the general two-interval family, the supports of any three consecutive colours are pairwise disjoint, including across colour zero. At $k=2g$ a base would require $2g$ distinct nonzero lengths among only $2g-1$ possibilities. For $g=2,3,4$, anchoring a run of the first support at zero yields respectively 8, 12 and 16 window-valid pairs. Every pair is a member of the stated family or its reflection. [Cyclic windows](../../lean/Conjectures/CircularSmallInsertionBlocks.lean) · [Terminal case](../../lean/Conjectures/CircularSmallInsertionTerminal.lean) · [Finite classification](../../lean/Conjectures/CircularSmallInsertionClassification.lean).

## Connectivity and retaining blocks

For every $g\ge15$ and every allowed packing, any two vertices have a common neighbor by the proved degree formula. Thus the constructed graph is connected. Keeping just the first block, or the first two blocks, produces subgraphs of that same labelled graph. Lean verifies the adjusted colour windows, maximum degrees $4g+1$ and $4g+2$, and exact indices $\Delta+2/3$ in both cases. [Connectivity](../../lean/Conjectures/CircularThreeBlockConnected.lean) · [Retained subgraphs and their indices](../../lean/Conjectures/CircularThreeBlockPrefixes.lean).

Independent research and publication runs each strictly rebuilt and replayed 67 Lean modules for these additional assertions. Each audit checked all 2,394 declarations, including 2,014 theorems, 542 private declarations and all 81 public theorem endpoints in the new files. The earlier receipts cover Theorem A, Proposition B and Corollary C. [Additional receipt](verification/forward-receipt.json) · [Full source list](../../lean/Conjectures/CircularThreeBlockAdditional.lean) · [Uniform theorem and finite receipts](../circular-index-upper-half-remaining-deltas/FORMALIZATION.md).

If you use an example, please credit @aadrianvv and cite both Cinna Davis’s site and the proof or graph you used. [Cinna Davis](https://itsdavis.com/) · [Source record](https://github.com/1337isnot1337/solved-conjectures/tree/main/results/circular-index-upper-half-delta-3-mod-4).
