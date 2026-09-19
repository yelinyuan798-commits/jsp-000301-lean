# JSP-000301: consecutive powerful numbers

This Lean 4 project formalizes the **no** answer to the [official JSP-000301
yes/no question](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#jsp-000301):
two consecutive positive powerful integers need not include a perfect square.
The counterexample is `12167` and `12168`.

The mathematical counterexample is **not new**. The official catalog credits
Solomon W. Golomb, *Powerful numbers*, *American Mathematical Monthly* 77(8)
(1970), 848–852, [DOI: 10.2307/2317020](https://doi.org/10.2307/2317020).
This repository is an AI-assisted formalization of that known result; it does
not claim discovery of the mathematics or priority over earlier Lean submissions.

Attribution: @yelinyuan798-commits requested and directed this project and owns
the publication repository. OpenAI Codex generated and checked the Lean code
under that direction. Repository ownership does not, by itself, establish
individual authorship or prize eligibility; the organizers determine those.

## Scope and definitions

`JustinSunProofs/Basic.lean` defines a prime as an integer at least two whose
only divisors are one and itself. It defines `IsPowerful n` by the standard
prime-divisor condition: for every prime `p` dividing `n`, `p * p` divides `n`.
For positive integers this is equivalent to saying that every prime in the
prime factorization has exponent at least two. `IsSquare n` means that some
natural number `k` satisfies `k * k = n`.

The file proves a general lemma: if `b ∣ a`, then `a * a * b` is powerful.
It applies this to `23 * 23 * 23 = 12167` and `78 * 78 * 2 = 12168`.
Both integers lie strictly between `110 * 110` and `111 * 111`, so neither is
a square. The final theorem `jsp_000301_answer_no` negates the universal
statement of the yes/no question for positive consecutive integers.

This proves the **yes/no counterexample**. It does not address the separate
counting question about how many such pairs exist.

## Reproduce

Use the Lean toolchain pinned in `lean-toolchain` (Lean 4 v4.34.0):

```sh
lake build
lake env leanchecker JustinSunProofs.Basic
```

The `#print axioms jsp_000301_answer_no` command at the end of the source
prints the final theorem's dependencies. It should list only Lean's standard
`propext` and `Quot.sound`, with no `sorryAx` or custom axioms. This project
has no Mathlib dependency.

This is a public proof repository, not an award determination. The official
program decides scope, originality, priority, and award eligibility. The
official catalog currently lists the mathematical question as solved and
contains no accepted Lean proof; multiple other public Lean submissions may
already exist and must be considered for priority.
