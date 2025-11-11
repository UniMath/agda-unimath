# Multiplication by positive, negative, and nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplication-positive-and-negative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.multiplication-closed-intervals-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.functoriality-disjunction
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.existential-quantification

open import order-theory.posets

open import real-numbers.dedekind-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

When we have information about the sign of the factors of a
[product](real-numbers.multiplication-real-numbers.md) of
[real numbers](real-numbers.dedekind-real-numbers.md), we can deduce the sign of
their product too.

## Lemmas

### The product of a positive and a negative real number is negative

```agda
abstract
  is-negative-mul-positive-negative-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → is-positive-ℝ x → is-negative-ℝ y →
    is-negative-ℝ (x *ℝ y)
  is-negative-mul-positive-negative-ℝ {x = x} {y = y} is-pos-x is-neg-y =
    preserves-le-right-sim-ℝ
      ( x *ℝ y)
      ( x *ℝ zero-ℝ)
      ( zero-ℝ)
      ( right-zero-law-mul-ℝ x)
      ( preserves-le-left-mul-ℝ⁺ (x , is-pos-x) is-neg-y)

mul-positive-negative-ℝ :
  {l1 l2 : Level} → ℝ⁺ l1 → ℝ⁻ l2 → ℝ⁻ (l1 ⊔ l2)
mul-positive-negative-ℝ (x , is-pos-x) (y , is-neg-y) =
  ( x *ℝ y , is-negative-mul-positive-negative-ℝ is-pos-x is-neg-y)
```

### The product of a negative and a positive real number is negative

```agda
abstract
  is-negative-mul-negative-positive-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → is-negative-ℝ x → is-positive-ℝ y →
    is-negative-ℝ (x *ℝ y)
  is-negative-mul-negative-positive-ℝ {x = x} {y = y} x<0 0<y =
    tr
      ( is-negative-ℝ)
      ( commutative-mul-ℝ y x)
      ( is-negative-mul-positive-negative-ℝ 0<y x<0)

mul-negative-positive-ℝ :
  {l1 l2 : Level} → ℝ⁻ l1 → ℝ⁺ l2 → ℝ⁻ (l1 ⊔ l2)
mul-negative-positive-ℝ (x , is-neg-x) (y , is-pos-y) =
  ( x *ℝ y , is-negative-mul-negative-positive-ℝ is-neg-x is-pos-y)
```

### If the product of two real numbers is positive, both are negative or both are positive

```agda
abstract opaque
  unfolding mul-ℝ

  same-sign-is-positive-mul-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → is-positive-ℝ (x *ℝ y) →
    type-disjunction-Prop
      ( is-negative-prop-ℝ x ∧ is-negative-prop-ℝ y)
      ( is-positive-prop-ℝ x ∧ is-positive-prop-ℝ y)
  same-sign-is-positive-mul-ℝ x y 0<xy =
    let
      open
        do-syntax-trunc-Prop
          ( ( is-negative-prop-ℝ x ∧ is-negative-prop-ℝ y) ∨
            ( is-positive-prop-ℝ x ∧ is-positive-prop-ℝ y))
      open inequality-reasoning-Poset ℚ-Poset
    in do
      ( q⁺@(q , is-pos-q) , q<xy) ←
        exists-ℚ⁺-in-lower-cut-is-positive-ℝ (x *ℝ y) 0<xy
      ( ( ax<x<bx@([ax,bx]@((ax , bx) , _) , ax<x , x<bx) ,
          ay<y<by@([ay,by]@((ay , by) , _) , ay<y , y<by)) ,
          q<[ax,bx][ay,by]) ← q<xy
      rec-coproduct
        ( λ (_ , is-neg-bx , _ , is-neg-by) →
          inl-disjunction
            ( is-negative-exists-ℚ⁻-in-upper-cut-ℝ
                ( x)
                ( intro-exists (bx , is-neg-bx) x<bx) ,
              is-negative-exists-ℚ⁻-in-upper-cut-ℝ
                ( y)
                ( intro-exists (by , is-neg-by) y<by)))
        ( λ (is-pos-ax , _ , is-pos-ay , _) →
          inr-disjunction
            ( is-positive-exists-ℚ⁺-in-lower-cut-ℝ
                ( x)
                ( intro-exists (ax , is-pos-ax) ax<x) ,
              is-positive-exists-ℚ⁺-in-lower-cut-ℝ
                ( y)
                ( intro-exists (ay , is-pos-ay) ay<y)))
        ( same-sign-bounds-is-positive-lower-bound-mul-closed-interval-ℚ
          ( [ax,bx])
          ( [ay,by])
          ( is-positive-le-ℚ⁺ q⁺ q<[ax,bx][ay,by]))
```

### If the product of two real numbers is negative, one is positive and the other negative

```agda
abstract
  different-signs-is-negative-mul-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → is-negative-ℝ (x *ℝ y) →
    type-disjunction-Prop
      ( is-negative-prop-ℝ x ∧ is-positive-prop-ℝ y)
      ( is-positive-prop-ℝ x ∧ is-negative-prop-ℝ y)
  different-signs-is-negative-mul-ℝ x y xy<0 =
    map-disjunction
      {!   !}
      {!   !}
      ( same-sign-is-positive-mul-ℝ
        ( neg-ℝ x)
        ( y)
        ( inv-tr
          ( is-positive-ℝ)
          ( left-negative-law-mul-ℝ x y)
          {!   !}))
```
