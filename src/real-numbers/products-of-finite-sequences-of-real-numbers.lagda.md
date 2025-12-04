# Products of finite sequences of real numbers

```agda
module real-numbers.products-of-finite-sequences-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.sums-of-finite-sequences-of-elements-commutative-monoids

open import lists.finite-sequences

open import real-numbers.dedekind-real-numbers
open import real-numbers.large-multiplicative-monoid-of-real-numbers
```

</details>

## Idea

The
{{#concept "product operation" Disambiguation="of a finite sequence of real numbers" Agda=product-fin-sequence-ℝ}}
extends the [multiplication](real-numbers.multiplication-real-numbers.md)
operation on [real numbers](real-numbers.dedekind-real-numbers.md) to any
[finite sequence](lists.finite-sequences.md) of real numbers.

## Definition

```agda
product-fin-sequence-ℝ : {l : Level} (n : ℕ) → fin-sequence (ℝ l) n → ℝ l
product-fin-sequence-ℝ {l} =
  sum-fin-sequence-type-Commutative-Monoid (commutative-monoid-mul-ℝ l)
```

## Properties

### Permutations preserve products

```agda
abstract
  preserves-product-permutation-fin-sequence-ℝ :
    {l : Level} (n : ℕ) (σ : Permutation n) (a : fin-sequence (ℝ l) n) →
    product-fin-sequence-ℝ n a ＝ product-fin-sequence-ℝ n (a ∘ map-equiv σ)
  preserves-product-permutation-fin-sequence-ℝ {l} =
    preserves-sum-permutation-fin-sequence-type-Commutative-Monoid
      ( commutative-monoid-mul-ℝ l)
```
