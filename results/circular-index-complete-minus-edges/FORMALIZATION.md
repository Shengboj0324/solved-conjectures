# Lean verification of the 32 deleted-edge colourings

For each of @aadrianvv’s 32 labelled graphs, Lean constructs the complete simple graph on the stated vertices and deletes exactly the listed unordered pairs. If the graph has $n$ vertices and $E$ edges and the supplied colouring has parameters $(p,q)$, Lean proves

```math
\frac{E}{\lfloor n/2\rfloor}\leq\chi'_c(G)\leq\frac pq .
```

The lower bound holds for every real-circle colouring. For the upper bound, Lean gives each edge its stored colour, identifies the opposite endpoint at each occupied colour and checks the cyclic gap up to the next allowed colour. [Graph and colouring proofs](../../lean/Conjectures/CircularDeletedColoring.lean) · [Original witness data](colourings.json).

The two bounds agree in 14 cases. Six other graphs, of maximum degrees 10, 14, 18, 22, 26 and 46, lie strictly between the maximum degree plus one half and the maximum degree plus one. In particular, deleting the two specified disjoint edges from the complete graph on 11 vertices gives an index between $53/5$ and $32/3$. The upper bound already refutes the proposed equality to 11. The stronger lower bound needed for exact equality to $32/3$, the single-edge theorem for arbitrary odd order, and the remaining sequencing and SAT exclusions are outside this receipt. [Eleven-vertex proof](../../lean/Conjectures/CircularDeletedWitness11.lean) · [Counterexample](../../lean/Conjectures/CircularDeletedWitnesses.lean) · [Written results](PROOF.md).

The same receipt covers eleven graphs built by inserting blocks of matchings. The source-data check compares every Lean table with the published JSON, covering 4,655 deleted-graph edges and 13,452 insertion-graph edges. It also checks the inverse tables and the insertion graphs’ degree tables. [One and two insertion blocks](../circular-index-upper-half-delta-2-mod-4/FORMALIZATION.md) · [Three insertion blocks](../circular-index-upper-half-delta-3-mod-4/FORMALIZATION.md) · [Source-data check](check_lean_data.py).

Independent research and publication runs each strictly compiled and replayed 35 project modules. Each axiom audit covered 822 declarations, including 617 theorems, 158 private declarations and all 71 required endpoints. The six largest vertex tables that exceeded the package memory limit now use kernel-checked groups of sixteen vertices. [Joint verification receipt](verification/lean-receipt.json).

Run these commands from the repository root to repeat the source-data comparison, strict source compilation, axiom audit and stock-kernel replay.

```bash
python3 results/circular-index-complete-minus-edges/check_lean_data.py
receipt=results/circular-index-complete-minus-edges/verification/lean-receipt.json
mapfile -t names < <(jq -r '.required_endpoints[]' "$receipt")
args=()
for name in "${names[@]}"; do
  args+=(--require "$name")
done
python3 scripts/verify_lean_target.py --root Conjectures.CircularFiniteIndexTheorems \
  "${args[@]}" --per-module-replay --out /tmp/circular-index-finite
```

If you use an example, please credit @aadrianvv for the construction, Mazák and Zrubák for the source question, and cite both Cinna Davis’s site and the specific graph or proof record used. [Cinna Davis](https://itsdavis.com/) · [Witness records](https://github.com/1337isnot1337/solved-conjectures/tree/main/results/circular-index-complete-minus-edges) · [Source question, Section 8](https://arxiv.org/html/2603.08822#S8).
