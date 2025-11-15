# Addition of nonzero real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.addition-nonzero-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.functoriality-disjunction
open import foundation.universe-levels

open import real-numbers.addition-negative-real-numbers
open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.nonzero-real-numbers
```

</details>

## Idea

On this page we describe properties of
[addition](real-numbers.addition-real-numbers.md) of
[nonzero](real-numbers.nonzero-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md).

## Properties

### If `x + y` is nonzero, `x` is nonzero or `y` is nonzero

```agda
abstract
  is-nonzero-either-is-nonzero-add-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) →
    is-nonzero-ℝ (x +ℝ y) →
    disjunction-type (is-nonzero-ℝ x) (is-nonzero-ℝ y)
  is-nonzero-either-is-nonzero-add-ℝ x y =
    elim-disjunction
      ( is-nonzero-prop-ℝ x ∨ is-nonzero-prop-ℝ y)
      ( λ x+y<0 →
        map-disjunction
          ( inl-disjunction)
          ( inl-disjunction)
          ( is-negative-either-is-negative-add-ℝ x y x+y<0))
      ( λ 0<x+y →
        map-disjunction
          ( inr-disjunction)
          ( inr-disjunction)
          ( is-positive-either-is-positive-add-ℝ x y 0<x+y))
```
