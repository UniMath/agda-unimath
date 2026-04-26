# Sylvester's sequence

```agda
module elementary-number-theory.sylvesters-sequence where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.ordinal-induction-natural-numbers
open import elementary-number-theory.products-of-natural-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

{{#concept "Sylvester's sequence" WD="Sylvester's sequence" WDID=Q2293800 Agda=sylvesters-sequence-ℕ}}
is the [sequence](lists.sequences.md) `s` of
[natural numbers](elementary-number-theory.natural-numbers.md) in which `s n` is
the successor of the
[product](elementary-number-theory.products-of-natural-numbers.md) of all the
numbers `s i` for `i < n`, i.e.,

$$
  s_n := 1+\left(\prod_{i<n}s_i\right).
$$

The first few entries in this sequence are `s 0 = 2`, `s 1 = 3`, `s 2 = 7`, and
`s 3 = 43`.

Sylvester's sequence is listed as [A000058](https://oeis.org/A000058) in the
[OEIS](literature.oeis.md) {{#cite oeis}}.

## Definitions

```agda
sylvesters-sequence-ℕ : ℕ → ℕ
sylvesters-sequence-ℕ =
  ordinal-ind-ℕ
    ( λ _ → ℕ)
    ( λ n f →
      succ-ℕ (Π-ℕ n (λ i → f (nat-Fin n i) (strict-upper-bound-nat-Fin n i))))
```

## References

{{#bibliography}}
