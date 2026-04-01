# Tuples

```agda
module lists.tuples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import lists.finite-sequences
```

</details>

## Idea

For every [natural number](elementary-number-theory.natural-numbers.md) `n` we
define {{#concept "tuples" WD="n-tuple" WDID=Q600590 Agda=tuple}} of length `n`.
These are [equivalent](lists.equivalence-tuples-finite-sequences.md) to the
related concept of [finite sequences](lists.finite-sequences.md), but are
structured like [lists](lists.lists.md) instead of [arrays](lists.arrays.md).

## Definitions

### The type of tuples

```agda
infixr 10 _∷_

data tuple {l : Level} (A : UU l) : ℕ → UU l where
  empty-tuple : tuple A zero-ℕ
  _∷_ : {n : ℕ} → A → tuple A n → tuple A (succ-ℕ n)

module _
  {l : Level} {A : UU l}
  where

  head-tuple : {n : ℕ} → tuple A (succ-ℕ n) → A
  head-tuple (x ∷ v) = x

  tail-tuple : {n : ℕ} → tuple A (succ-ℕ n) → tuple A n
  tail-tuple (x ∷ v) = v

  snoc-tuple : {n : ℕ} → tuple A n → A → tuple A (succ-ℕ n)
  snoc-tuple empty-tuple a = a ∷ empty-tuple
  snoc-tuple (x ∷ v) a = x ∷ (snoc-tuple v a)

  component-tuple :
    (n : ℕ) → tuple A n → fin-sequence A n
  component-tuple (succ-ℕ n) (a ∷ v) (inl k) = component-tuple n v k
  component-tuple (succ-ℕ n) (a ∷ v) (inr k) = a
```

## Properties

### Adding the tail to the head gives the same tuple

```agda
module _
  {l : Level} {A : UU l}
  where

  cons-head-tail-tuple :
    (n : ℕ) →
    (v : tuple A (succ-ℕ n)) →
    ((head-tuple v) ∷ (tail-tuple v)) ＝ v
  cons-head-tail-tuple n (x ∷ v) = refl
```

### Computing the transport of a tuple over its size

```agda
compute-tr-tuple :
  {l : Level} {A : UU l}
  {n m : ℕ} (p : succ-ℕ n ＝ succ-ℕ m) (v : tuple A n) (x : A) →
  tr (tuple A) p (x ∷ v) ＝
  (x ∷ tr (tuple A) (is-injective-succ-ℕ p) v)
compute-tr-tuple refl v x = refl
```
