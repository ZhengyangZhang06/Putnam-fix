# Why `putnam_1974_b1` Is False As Formalized

The JSONL formal statement for `putnam_1974_b1` is not provable because the
right-hand side is too weak.

The formalized theorem says that a unit-circle configuration `p` is maximal for
the sum of all pairwise distances iff:

```lean
∃ᵉ (B > 0) (o : Equiv.Perm (Fin 5)),
  ∀ i, dist (p (o i)) (p (o (i + 1))) = B
```

Here `∃ᵉ` is ordinary existential notation with side conditions, not uniqueness.
So this only requires that the five indexed points can be ordered in a cycle
whose consecutive distances are all equal. It does not require the five points
to be distinct, and it does not force a regular pentagon.

Counterexample: let `A`, `B`, and `C` be the three vertices of an equilateral
triangle on the unit circle, and define the five points as:

```text
A, B, C, A, B
```

Using the identity permutation, all five consecutive cyclic distances are
`sqrt 3`, so the RHS of the formal statement holds. However, the total pairwise
distance sum for this configuration is:

```text
8 * sqrt 3
```

A different valid unit-circle configuration, for example:

```text
A, A, (-1, 0), (0, 1), (0, -1)
```

has total pairwise distance:

```text
6 + 6 * sqrt 2
```

Lean checked the strict inequality:

```text
8 * sqrt 3 < 6 + 6 * sqrt 2
```

Therefore the RHS can hold for a configuration that is not maximal. This
contradicts the `iff` in the JSONL formal statement.

So the original Putnam problem is not the issue; the JSONL formalization is
incorrect as written. The copied file `Putnam1974B1.lean` is left with its
original `sorry` because filling it would require proving a false theorem.
