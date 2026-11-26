# The seventeen nonregular circular-colouring certificates

For each nonregular graph of Section 7.3, Lean proves that the maximum degree is the reported integer and that the real circular chromatic index equals $`\Delta+2/3`$. The result covers the exceptional graph with $`\Delta=21`$ and both graphs at each $`g=6,\ldots,13`$. The latter have $`6g+1`$ vertices and maximum degrees $`4g+1`$ and $`4g+2`$. Their degree pairs range from 25 and 26 through 53 and 54. [Original construction](PROOF.md) · [Stored certificates](data/part2_certificates.json) · [Lean entry point](../../lean/Conjectures/CircularInsertionStoredBases.lean).

Each certificate supplies an edge-colour table and the degree of every vertex. Lean verifies simplicity, the circular separation of incident edge colours, attainment of the maximum degree at vertex zero, and the lower bound from the number of edges and the maximum size of a matching on an odd number of vertices. The resulting equality uses the infimum over real circular edge-colourings. The Python comparison reconstructs each original colouring and matches all 19,649 labelled edge colours to the Lean tables. Some of these graphs also occur in the proofs of the uniform insertion families. [Degree-21 example](../../lean/Conjectures/CircularInsertionDegree21.lean) · [Last degree pair](../../lean/Conjectures/CircularInsertionDegree54.lean) · [Table comparison](check_lean_insertions.py).

## Verification

Independent research and publication runs each strictly compiled and replayed 28 project modules. Each axiom audit covered 474 declarations, including 342 theorems, 85 private declarations and all 18 required endpoints. The six largest vertex tables that exceeded the package memory limit now use kernel-checked groups of sixteen vertices. [Section 7.3 receipt](verification/insertion-receipt.json) · [Earlier regular-graph receipt](../../docs/verification/lean-named-20261121/circular-receipt.json).

From the repository root, the original certificates and their transfer to Lean can be checked with these commands.

```sh
python3 results/circular-index-upper-half-circulants/verify_part2.py
python3 results/circular-index-upper-half-circulants/check_lean_insertions.py
python3 scripts/verify_lean_target.py --root Conjectures.CircularInsertionStoredBases --require CircularIndex.Deleted.Degree21.exact_index_and_degree --require CircularIndex.Deleted.Degree54.exact_index_and_degree --out /tmp/circular-stored
```

The ranked result remains partial. Its two main theorems, the regular C31 and C33 examples, and the 17 nonregular positive examples have Lean proofs. The additional general structural and insertion lemmas and the full collection of finite search exclusions have separate statements in the written proof.

If you use these certificates, please credit @aadrianvv for the construction and cite both Cinna Davis’s site and the specific proof or graph record you used. [Cinna Davis](https://itsdavis.com/) · [Source record](https://github.com/1337isnot1337/solved-conjectures/tree/main/results/circular-index-upper-half-circulants).
