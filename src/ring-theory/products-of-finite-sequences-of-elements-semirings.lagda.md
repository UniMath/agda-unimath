# Products of finite sequences of elements of semirings

```agda
module ring-theory.products-of-finite-sequences-of-elements-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import group-theory.sums-of-finite-sequences-of-elements-monoids

open import linear-algebra.finite-sequences-in-semirings

open import lists.finite-sequences

open import ring-theory.semirings
```

</details>

## Idea

The
{{#concept "product operation" Disambiguation="over finite sequences in a semiring" Agda=product-fin-sequence-type-Semiring}}
extends the binary multiplication operation on a
[semiring](ring-theory.semirings.md) `R` to any
[finite sequence](lists.finite-sequences.md) of elements of `R`.

## Definition

```agda
product-fin-sequence-type-Semiring :
  {l : Level} (R : Semiring l) (n : ℕ) →
  fin-sequence-type-Semiring R n → type-Semiring R
product-fin-sequence-type-Semiring R =
  sum-fin-sequence-type-Monoid (multiplicative-monoid-Semiring R)
```
