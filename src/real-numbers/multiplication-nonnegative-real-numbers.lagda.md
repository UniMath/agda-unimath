# Multiplication of nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplication-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.multiplication-closed-intervals-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
```

</details>

## Idea

The
{{#concept "product" Disambiguation="of nonnegative real numbers" Agda=mul-ℝ⁰⁺}}
of two [nonnegative real numbers](real-numbers.nonnegative-real-numbers.md) is
their [product](real-numbers.multiplication-real-numbers.md) as
[real numbers](real-numbers.dedekind-real-numbers.md), and is itself
nonnegative.

## Definition

```agda
abstract opaque
  unfolding mul-ℝ

  is-nonnegative-mul-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} →
    is-nonnegative-ℝ x → is-nonnegative-ℝ y → is-nonnegative-ℝ (x *ℝ y)
  is-nonnegative-mul-ℝ {x = x} {y = y} 0≤x 0≤y =
    is-nonnegative-is-positive-upper-cut-ℝ
      ( x *ℝ y)
      ( λ q xy<q →
        let open do-syntax-trunc-Prop (is-positive-prop-ℚ q)
        in do
          ( ( ([a,b]@((a , b) , _) , a<x , x<b) ,
              ([c,d]@((c , d) , _) , c<y , y<d)) ,
            [a,b][c,d]<q) ← xy<q
          let
            b⁺ = (b , is-positive-is-in-upper-cut-ℝ⁰⁺ (x , 0≤x) x<b)
            d⁺ = (d , is-positive-is-in-upper-cut-ℝ⁰⁺ (y , 0≤y) y<d)
          is-positive-le-ℚ⁺
            ( b⁺ *ℚ⁺ d⁺)
            ( concatenate-leq-le-ℚ
              ( b *ℚ d)
              ( upper-bound-mul-closed-interval-ℚ [a,b] [c,d])
              ( q)
              ( transitive-leq-ℚ _ _ _
                ( leq-right-max-ℚ _ _)
                ( leq-right-max-ℚ _ _))
              ( [a,b][c,d]<q)))

mul-ℝ⁰⁺ : {l1 l2 : Level} → ℝ⁰⁺ l1 → ℝ⁰⁺ l2 → ℝ⁰⁺ (l1 ⊔ l2)
mul-ℝ⁰⁺ (x , 0≤x) (y , 0≤y) = (x *ℝ y , is-nonnegative-mul-ℝ 0≤x 0≤y)

infixl 40 _*ℝ⁰⁺_
_*ℝ⁰⁺_ : {l1 l2 : Level} → ℝ⁰⁺ l1 → ℝ⁰⁺ l2 → ℝ⁰⁺ (l1 ⊔ l2)
_*ℝ⁰⁺_ = mul-ℝ⁰⁺

ap-mul-ℝ⁰⁺ :
  {l1 l2 : Level} → {x x' : ℝ⁰⁺ l1} → x ＝ x' → {y y' : ℝ⁰⁺ l2} → y ＝ y' →
  x *ℝ⁰⁺ y ＝ x' *ℝ⁰⁺ y'
ap-mul-ℝ⁰⁺ = ap-binary mul-ℝ⁰⁺
```

## Properties

### Multiplication by a nonnegative real number preserves inequality

```agda
abstract
  preserves-order-left-mul-ℝ⁰⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁰⁺ l1) {y : ℝ l2} {z : ℝ l3} → leq-ℝ y z →
    leq-ℝ (real-ℝ⁰⁺ x *ℝ y) (real-ℝ⁰⁺ x *ℝ z)
  preserves-order-left-mul-ℝ⁰⁺ x⁰⁺@(x , 0≤x) {y} {z} y≤z =
    leq-is-nonnegative-diff-ℝ
      ( x *ℝ y)
      ( x *ℝ z)
      ( tr
        ( is-nonnegative-ℝ)
        ( left-distributive-mul-diff-ℝ x z y)
        ( is-nonnegative-mul-ℝ
          ( 0≤x)
          ( is-nonnegative-diff-leq-ℝ y≤z)))

  preserves-order-right-mul-ℝ⁰⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁰⁺ l1) {y : ℝ l2} {z : ℝ l3} → leq-ℝ y z →
    leq-ℝ (y *ℝ real-ℝ⁰⁺ x) (z *ℝ real-ℝ⁰⁺ x)
  preserves-order-right-mul-ℝ⁰⁺ x y≤z =
    binary-tr
      ( leq-ℝ)
      ( commutative-mul-ℝ _ _)
      ( commutative-mul-ℝ _ _)
      ( preserves-order-left-mul-ℝ⁰⁺ x y≤z)

  preserves-order-mul-ℝ⁰⁺ :
    {l1 l2 l3 l4 : Level} →
    (x : ℝ⁰⁺ l1) (x' : ℝ⁰⁺ l2) (y : ℝ⁰⁺ l3) (y' : ℝ⁰⁺ l4) →
    leq-ℝ⁰⁺ x x' → leq-ℝ⁰⁺ y y' → leq-ℝ⁰⁺ (x *ℝ⁰⁺ y) (x' *ℝ⁰⁺ y')
  preserves-order-mul-ℝ⁰⁺ x x' y y' x≤x' y≤y' =
    transitive-leq-ℝ _ _ _
      ( preserves-order-right-mul-ℝ⁰⁺ y' x≤x')
      ( preserves-order-left-mul-ℝ⁰⁺ x y≤y')
```

### Unit laws

```agda
abstract
  left-unit-law-mul-ℝ⁰⁺ : {l : Level} (x : ℝ⁰⁺ l) → one-ℝ⁰⁺ *ℝ⁰⁺ x ＝ x
  left-unit-law-mul-ℝ⁰⁺ (x , _) = eq-ℝ⁰⁺ _ _ (left-unit-law-mul-ℝ x)
```

### If `x` is a nonnegative real number less than or equal to 1 and `y` is nonnegative, `xy ≤ y`

```agda
abstract
  leq-left-mul-leq-one-ℝ⁰⁺ :
    {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) →
    leq-ℝ⁰⁺ x one-ℝ⁰⁺ → leq-ℝ⁰⁺ (x *ℝ⁰⁺ y) y
  leq-left-mul-leq-one-ℝ⁰⁺ x y x≤1 =
    tr
      ( leq-ℝ⁰⁺ (x *ℝ⁰⁺ y))
      ( left-unit-law-mul-ℝ⁰⁺ y)
      ( preserves-order-right-mul-ℝ⁰⁺ y x≤1)
```
