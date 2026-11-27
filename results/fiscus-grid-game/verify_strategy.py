#!/usr/bin/env python3
"""Replay the response certificate in PROOF.md without searching for a strategy."""

from pathlib import Path
from re import fullmatch

V = {f"{row}{j}" for row in "AB" for j in range(1, 8)}
FIRST = "A2"


def neighbourhood(v):
    """Generate the closed grid neighbourhood directly from coordinates."""
    return {w for w in V if
            (v[0] != w[0]) + abs(int(v[1]) - int(w[1])) <= 1}


N = {v: neighbourhood(v) for v in V}


def outstanding(picked):
    return {v for v in V if not (N[v] & picked)}


def passes(picked):
    return V - picked - set().union(*(N[v] for v in outstanding(picked)))


def check_endgame(picked):
    u, v = sorted(outstanding(picked))
    assert not N[u] & N[v], (picked, u, v)
    assert {len(N[u]), len(N[v])} == {3, 4}
    assert len(passes(picked)) % 2 == 0


def verify_exception(picked):
    if picked == {"A1", "A2", "A6", "B1"}:
        picked = picked | {"A4"}
        assert outstanding(picked) == {"B3", "B5", "B7"}
        assert not passes(picked)
        for x in V - picked:
            residual = picked | {x}
            assert outstanding(residual)
            if x in {"A5", "B5"}:
                y, = {"A5", "B5"} - {x}
                assert y not in residual
                check_endgame(residual | {y})
            else:
                choices = set.intersection(*(N[v] for v in outstanding(residual)))
                assert choices and not choices & residual
                assert not outstanding(residual | {min(choices)})
    elif picked == {"A2", "A4", "A5", "B5"}:
        picked = picked | {"A1"}
        assert outstanding(picked) == {"B3", "A7", "B7"}
        assert passes(picked) == {"B1"}
        for x in V - picked:
            residual = picked | {x}
            assert outstanding(residual)
            if x in N["B3"]:
                reply, finish = "A7", True
            elif x in N["A7"] & N["B7"]:
                reply, finish = "B3", True
            elif x in N["A7"] | N["B7"]:
                reply, finish = "B1", False
            else:
                assert x == "B1"
                reply, finish = "A6", False
            assert reply not in residual
            if finish:
                assert not outstanding(residual | {reply})
            else:
                check_endgame(residual | {reply})
    else:
        raise AssertionError(f"Unexpected fourth-move state: {sorted(picked)}")


def parse():
    rows = []
    proof = Path(__file__).with_name("PROOF.md").read_text(encoding="utf-8")
    for line in proof.splitlines():
        if not fullmatch(r"\| [AB]\d/[AB]\d \|.*", line):
            continue
        opening, witnesses, pairs, exception = (x.strip() for x in line.split("|")[1:-1])
        witness = {x.strip() for x in witnesses.split(",")}
        replies = []
        for item in pairs.split(";"):
            move_pair, label = (x.strip() for x in item.split(":"))
            remaining = set() if label == "–" else set(label.split(","))
            d, e = move_pair.split("/")
            replies.append((d, e, remaining))
        rows.append((opening.split("/"), witness, replies, exception))
    assert len(rows) == 7
    return rows


def replay():
    legal_second = set()
    distinct_tables = set()
    for (b, c), witness, replies, exception in parse():
        transforms = [{v: v for v in V}]
        if (b, c) == ("A1", "A6"):
            swap = dict(transforms[0], A1="B1", B1="A1")
            assert all(
                ("A1" in N[v]) == ("B1" in N[v])
                for v in outstanding({FIRST})
            )
            transforms.append(swap)
        for tau in transforms:
            d0, e0 = tau[b], tau[c]
            if tau is transforms[-1] and len(transforms) == 2:
                # The exchange is needed only when B1 is the first opponent move.
                legal_second.add(d0)
            else:
                legal_second.update([d0, e0])
            assert all(outstanding({FIRST, x}) for x in (d0, e0))
            picked = {FIRST, d0, e0}
            assert len(picked) == 3
            assert witness <= outstanding(picked)
            u, v = sorted(witness)
            assert not N[u] & N[v]
            covered = set()
            for d, e, annotated in replies:
                x, y = tau[d], tau[e]
                assert x != y and not (picked & {x, y})
                assert outstanding(picked | {x})
                assert outstanding(picked | {y})
                state = picked | {x, y}
                assert outstanding(state) == annotated, (picked, d, e)
                if annotated:
                    check_endgame(state)
                covered.update([x, y])
            if exception != "None":
                x = tau[exception]
                assert x not in picked and x not in covered
                assert outstanding(picked | {x})
                verify_exception(picked | {x})
                covered.add(x)
            assert covered == V - picked
            distinct_tables.add(frozenset(picked))
    assert legal_second == V - {FIRST}
    print(f"Verified all {len(legal_second)} second moves and {len(distinct_tables)} reply tables.")


if __name__ == "__main__":
    replay()
