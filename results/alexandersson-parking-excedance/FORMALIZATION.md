# Lean formalization of the parking excedance counterexample

Lean proves that the strict-excedance polynomial of the actual length-17
parking preference words has a nonreal complex root. A length-17 counterexample
suffices to refute the universal real-rootedness and interlacing conjecture.

The word model uses zero-based indices and the equivalent parking prefix
condition. The counting proof processes preference values in increasing order.
Stripping the last value recovers the previous state, the new marked positions,
and the mask that inserts the new unmarked copies. The two finite choices give
the binomial factors in the recurrence. A final bijection fills the unmarked
positions and recovers a parking word with a subset of its strict excedances.

The executable table computes the marked counts. Lean checks each intermediate
table from the preceding one using the same recurrence, then checks the
length-17 marked row and its conversion from powers of `X - 1` to the
published coefficient row. This bounds peak replay memory without changing
the theorem or using a native-code trust assumption. The table checks sit in their own module, which imports only natural-number factorials. Its smaller import baseline keeps the largest check within the `-M4500` memory cap that `lake build` applies on Linux runners. The negative Laguerre value at `-1/5` then gives the nonreal root of the
literal enumerator.

- [Word model](../../lean/Conjectures/AlexanderssonParkingExcedanceWords.lean)
- [Counting recurrence](../../lean/Conjectures/AlexanderssonParkingExcedanceCount.lean)
- [Parking-word bijection](../../lean/Conjectures/AlexanderssonParkingExcedanceEnumeration.lean)
- [Laguerre certificate](../../lean/Conjectures/AlexanderssonParkingExcedanceRoots.lean)
- [Table certificates](../../lean/Conjectures/AlexanderssonParkingExcedanceTables.lean)
- [Final theorem](../../lean/Conjectures/AlexanderssonParkingExcedance.lean)

The word model and Laguerre certificate reuse Cinna Davis’s research
checkpoints. [Word model commit](https://github.com/1337isnot1337/solved-conjectures/commit/37b703a3)
· [Laguerre certificate commit](https://github.com/1337isnot1337/solved-conjectures/commit/9d0ac239)

## Replay

From the repository root with the pinned Lean toolchain on the path, run:

```sh
python3 scripts/verify_lean_target.py \
  --root Conjectures.AlexanderssonParkingExcedance \
  --require AlexanderssonParkingExcedance.isParking_iff_sorted_permutation \
  --require AlexanderssonParkingExcedance.state_card_succ \
  --require AlexanderssonParkingExcedance.final_state_card \
  --require AlexanderssonParkingExcedance.polynomial_eq_state_sum \
  --require AlexanderssonParkingExcedance.polynomial17_eq_row \
  --require AlexanderssonParkingExcedance.row17_laguerre_neg \
  --require AlexanderssonParkingExcedance.parking_excedance_counterexample \
  --out results/alexandersson-parking-excedance/verification
```

The [receipt](verification/receipt.json) records strict compilation, the
all-owned axiom audit, and stock-kernel replay of the five-module closure.
