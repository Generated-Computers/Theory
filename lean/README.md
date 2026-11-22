# Lean formalizations

This directory contains Lean formalizations of results in this repository. They are organized in
a single library, as in the Lean library of the OpenAI mathematics release, and use the same
toolchain (Lean 4.34.1) and the same Mathlib commit (`d13f23b7`).

Every one of the 55 manuscripts of families 001–011 has at least one formalized main result; the
five manuscripts of family 012 are not formalized yet. The library has
104 files and about 28,000 lines. The 55 [Comparator](https://github.com/leanprover/comparator)
configurations list 472 main theorems. Every one of them is proved without `sorry`, and
`#print axioms` reports only `propext`, `Quot.sound` and `Classical.choice`.

**Scope.** The formalizations prove the mathematical content of the papers: the correctness of
reductions and constructions, combinatorial invariants, exact counts, algebraic identities,
finite group computations, and round counts of explicitly defined iterations. Complexity classes
(L, NC, P, BPNC, SC and the like), logspace computability, circuit depth and size, and
probability bounds are not formalized. So no Lean statement says that a problem is P-complete or
lies in NC. Each family's scope page in [`docs/`](docs/) says, manuscript by manuscript, what is
formalized and what is not. For example, for "Two Pages Suffice for P-Completeness" it proves
that every NOR circuit is mapped to a Sequential NOR instance of page number at most 2 whose last
trace bit is the circuit's output; the logspace computability of that map is not formalized.

## Layout

- `GC/<Area>/<Topic>/` — the proofs, one topic per result family; `GC/<Area>/<Topic>/Main.lean`
  imports everything of the topic, and [`GC.lean`](GC.lean) imports every topic.
- [`ComparatorChallenges/`](ComparatorChallenges/) — for each manuscript, a statement-only file
  (definitions copied verbatim from the solution, main theorems with `sorry`) and its JSON
  configuration.
- [`docs/`](docs/) — the scope of the formalization for each result family.
- [`formalization.yaml`](formalization.yaml) — the catalogue of formalized papers and main results.
- [`scripts/`](scripts/) — the checks described below.

| Family | Topic | Scope |
| --- | --- | --- |
| 001 | `GC/Computability/RandomSeqNOR` | [docs/001.md](docs/001.md) |
| 002 | `GC/Computability/NewtonStrahler` | [docs/002.md](docs/002.md) |
| 003 | `GC/Optimization/FlowCircuits` | [docs/003.md](docs/003.md) |
| 004 | `GC/GroupTheory/A5Programs` | [docs/004.md](docs/004.md) |
| 005 | `GC/Computability/Portals` | [docs/005.md](docs/005.md) |
| 006 | `GC/Computability/SeqNORNormalForms` | [docs/006.md](docs/006.md) |
| 007 | `GC/Computability/StructuralCompilers` | [docs/007.md](docs/007.md) |
| 008 | `GC/Computability/SCLadder` | [docs/008.md](docs/008.md) |
| 009 | `GC/Combinatorics/GridCompilers` | [docs/009.md](docs/009.md) |
| 010 | `GC/Computability/Tabulation` | [docs/010.md](docs/010.md) |
| 011 | `GC/Computability/Semisort` | [docs/011.md](docs/011.md) |

## Building and checking

```sh
lake exe cache get
lake build
python3 scripts/axioms.py               # axioms of all 472 main theorems
python3 scripts/check_statements.py .   # challenge statements = solution statements
```

`scripts/check_statements.py` builds each challenge module and compares it with the solution
module. For every listed theorem it checks the statement, and for every `GC.*` definition the
statement depends on it checks the type and the body. This is the statement-matching part of
what Comparator checks; the axiom part is `scripts/axioms.py`.
Proofs inside definitions are compared by their statements, and auxiliary `match` functions are
inlined, because their names depend on the order of elaboration. Comparator itself
(`lake env comparator ComparatorChallenges/<Name>.json`, see its README) needs `landrun`,
which runs only on Linux, and was not run.

No human has reviewed these formalizations yet.
