# Multiplication of nonzero real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplication-nonzero-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.invertible-elements-commutative-rings

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.large-ring-of-real-numbers
open import real-numbers.multiplication-negative-real-numbers
open import real-numbers.multiplication-positive-and-negative-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-nonzero-real-numbers
open import real-numbers.nonzero-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

The
{{#concept "product" Disambiguation="of pairs of nonzero real numbers" Agda=mul-nonzero-ℝ}}
of two [nonzero](real-numbers.nonzero-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md) is their
[product](real-numbers.multiplication-real-numbers.md) as real numbers, and is
itself nonzero.

## Definition

```agda
abstract
  is-nonzero-mul-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → is-nonzero-ℝ x → is-nonzero-ℝ y →
    is-nonzero-ℝ (x *ℝ y)
  is-nonzero-mul-ℝ {x = x} {y = y} x#0 y#0 =
    let
      motive = is-nonzero-prop-ℝ (x *ℝ y)
    in
      elim-disjunction
        ( motive)
        ( λ x<0 →
          elim-disjunction
            ( motive)
            ( inr-disjunction ∘ is-positive-mul-is-negative-ℝ x<0)
            ( inl-disjunction ∘ is-negative-mul-negative-positive-ℝ x<0)
            ( y#0))
        ( λ 0<x →
          elim-disjunction
            ( motive)
            ( inl-disjunction ∘ is-negative-mul-positive-negative-ℝ 0<x)
            ( inr-disjunction ∘ is-positive-mul-ℝ 0<x)
            ( y#0))
        ( x#0)

mul-nonzero-ℝ :
  {l1 l2 : Level} → nonzero-ℝ l1 → nonzero-ℝ l2 → nonzero-ℝ (l1 ⊔ l2)
mul-nonzero-ℝ (x , x#0) (y , y#0) =
  ( x *ℝ y , is-nonzero-mul-ℝ x#0 y#0)
```

## Properties

### If the product of two real numbers is nonzero, they are both nonzero

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  abstract
    is-nonzero-factors-is-nonzero-mul-ℝ :
      is-nonzero-ℝ (x *ℝ y) → is-nonzero-ℝ x × is-nonzero-ℝ y
    is-nonzero-factors-is-nonzero-mul-ℝ =
      let
        motive = is-nonzero-prop-ℝ x ∧ is-nonzero-prop-ℝ y
      in
        elim-disjunction
          ( motive)
          ( λ xy<0 →
            elim-disjunction
              ( motive)
              ( map-product inr-disjunction inl-disjunction)
              ( map-product inl-disjunction inr-disjunction)
              ( different-signs-is-negative-mul-ℝ x y xy<0))
          ( λ 0<xy →
            elim-disjunction
              ( motive)
              ( map-product inl-disjunction inl-disjunction)
              ( map-product inr-disjunction inr-disjunction)
              ( same-sign-is-positive-mul-ℝ x y 0<xy))
```

### If a real number has a multiplicative inverse, it is nonzero

```agda
abstract
  is-nonzero-has-right-inverse-mul-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → sim-ℝ (x *ℝ y) one-ℝ →
    is-nonzero-ℝ x
  is-nonzero-has-right-inverse-mul-ℝ x y xy=1 =
    pr1
      ( is-nonzero-factors-is-nonzero-mul-ℝ
        ( x)
        ( y)
        ( is-nonzero-is-positive-ℝ
          ( is-positive-sim-ℝ
            ( symmetric-sim-ℝ xy=1)
            ( is-positive-one-ℝ))))

  is-nonzero-has-left-inverse-mul-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → sim-ℝ (x *ℝ y) one-ℝ →
    is-nonzero-ℝ y
  is-nonzero-has-left-inverse-mul-ℝ x y xy=1 =
    is-nonzero-has-right-inverse-mul-ℝ y x
      ( tr (λ z → sim-ℝ z one-ℝ) (commutative-mul-ℝ x y) xy=1)

  is-nonzero-is-invertible-ℝ :
    {l : Level} (x : ℝ l) →
    is-invertible-element-Commutative-Ring (commutative-ring-ℝ l) x →
    is-nonzero-ℝ x
  is-nonzero-is-invertible-ℝ {l} x (y , xy=1 , _) =
    is-nonzero-has-right-inverse-mul-ℝ x y
      ( inv-tr
        ( λ z → sim-ℝ z one-ℝ)
        ( xy=1)
        ( symmetric-sim-ℝ
          { x = one-ℝ}
          { y = raise-ℝ l one-ℝ}
          ( sim-raise-ℝ l one-ℝ)))
```
