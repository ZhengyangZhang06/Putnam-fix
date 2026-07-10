# Why `putnam_2017_b3` Is False As Formalized

The JSONL formal statement for `putnam_2017_b3` is not provable because the
final expression is parsed differently from the intended mathematical
statement.

The informal problem asks to prove that `f(1/2)` is irrational. The formalized
Lean conclusion is:

```lean
f (2/3) = 3/2 -> Irrational (f 1/2)
```

In Lean, function application has higher precedence than division. Therefore
the expression

```lean
f 1/2
```

is parsed as:

```lean
(f 1) / 2
```

not as:

```lean
f (1 / 2)
```

So the theorem is asking for irrationality of `(f 1) / 2`, while the intended
Putnam problem asks for irrationality of `f (1 / 2)`.

The previous proof attempt checked this exact parse in Lean: `f 1/2 = f 1 / 2`
is accepted by reflexivity. It also produced kernel-checked diagnostic evidence
that, under the benchmark hypotheses and `f (2 / 3) = 3 / 2`, the parsed target
is refutable:

```lean
¬ Irrational (f 1 / 2)
```

This contradiction is possible because the formal hypothesis

```lean
hf : ∀ x, f x = ∑' n : ℕ, c n * x^n
```

is stated for every real `x`, including `x = 1`. At `x = 1`, the series need not
be summable, and Lean's `tsum` has a default value for nonsummable series. The
previous audit used this behavior to show that the exact parsed conclusion is
not a valid theorem.

The intended statement should at least parenthesize the final value as:

```lean
Irrational (f (1 / 2))
```

and may also need a more precise convergence-domain hypothesis for the power
series. The original Putnam problem is not the issue; the JSONL formalization is
incorrect as written.
