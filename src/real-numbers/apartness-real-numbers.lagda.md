# Apartness of real numbers

```agda
module real-numbers.apartness-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.identity-types
open import foundation.law-of-excluded-middle
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

Two real numbers are apart if one is strictly less than the other.
This definition is used in Section 11.2 in {{#cite UF13}}.

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  apart-ℝ-Prop : Prop (l1 ⊔ l2)
  apart-ℝ-Prop = le-ℝ-Prop x y ∨ le-ℝ-Prop y x

  apart-ℝ : UU (l1 ⊔ l2)
  apart-ℝ = type-Prop apart-ℝ-Prop
```

## Properties

### Apartness implies inequality

```agda
module _
  {l : Level}
  (x y : ℝ l)
  where

  nonequal-apart-ℝ : apart-ℝ x y → x ≠ y
  nonequal-apart-ℝ apart x=y =
    elim-disjunction
      ( empty-Prop)
      ( λ x<y → irreflexive-le-ℝ x (tr (le-ℝ x) (inv x=y) x<y))
      ( λ y<x → irreflexive-le-ℝ y (tr (le-ℝ y) x=y y<x))
      ( apart)
```

### If LEM, inequality implies apartness

```agda
module _
  {l : Level}
  (lem : LEM l)
  (x y : ℝ l)
  where

  apart-lem-nonequal-ℝ : x ≠ y → apart-ℝ x y
  apart-lem-nonequal-ℝ x≠y =
    rec-coproduct
      ( inl-disjunction)
      ( λ x≮y → rec-coproduct
          ( inr-disjunction)
          ( λ y≮x →
            reductio-ad-absurdum
              ( antisymmetric-leq-ℝ
                ( x)
                ( y)
                ( leq-not-le-ℝ y x y≮x)
                ( leq-not-le-ℝ x y x≮y))
              ( x≠y))
          ( lem (le-ℝ-Prop y x)))
      ( lem (le-ℝ-Prop x y))
```

## References

{{#bibliography}}
