# Multiplication of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplication-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.closed-intervals-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.multiplication-closed-intervals-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-positive-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

The
{{#concept "product" Disambiguation="of pairs of positive real numbers" Agda=mul-ℝ⁺}}
of two [positive](real-numbers.positive-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md) is their
[product](real-numbers.multiplication-real-numbers.md) as real numbers, and is
itself positive.

## Definition

```agda
module _
  {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2}
  where

  opaque
    unfolding mul-ℝ

    is-positive-mul-ℝ :
      is-positive-ℝ x → is-positive-ℝ y → is-positive-ℝ (x *ℝ y)
    is-positive-mul-ℝ 0<x 0<y =
      let open do-syntax-trunc-Prop (is-positive-prop-ℝ (x *ℝ y))
      in do
        (a⁺@(a , _) , a<x) ← exists-ℚ⁺-in-lower-cut-is-positive-ℝ x 0<x
        (b , x<b) ← is-inhabited-upper-cut-ℝ x
        (c⁺@(c , _) , c<y) ← exists-ℚ⁺-in-lower-cut-is-positive-ℝ y 0<y
        (d , y<d) ← is-inhabited-upper-cut-ℝ y
        let
          a<b = le-lower-upper-cut-ℝ x a b a<x x<b
          b⁺ = (b , is-positive-le-ℚ⁺ a⁺ b a<b)
          c<d = le-lower-upper-cut-ℝ y c d c<y y<d
          d⁺ = (d , is-positive-le-ℚ⁺ c⁺ d c<d)
          [a,b] = ((a , b) , leq-le-ℚ a<b)
          [c,d] = ((c , d) , leq-le-ℚ c<d)
        is-positive-exists-ℚ⁺-in-lower-cut-ℝ
          ( x *ℝ y)
          ( intro-exists
            ( min-ℚ⁺
              ( min-ℚ⁺ (a⁺ *ℚ⁺ c⁺) (a⁺ *ℚ⁺ d⁺))
              ( min-ℚ⁺ (b⁺ *ℚ⁺ c⁺) (b⁺ *ℚ⁺ d⁺)))
            ( leq-lower-cut-mul-ℝ'-lower-cut-mul-ℝ x y
              ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d])
              ( intro-exists
                ( ([a,b] , a<x , x<b) , ([c,d] , c<y , y<d))
                ( refl-leq-ℚ _))))

mul-ℝ⁺ : {l1 l2 : Level} → ℝ⁺ l1 → ℝ⁺ l2 → ℝ⁺ (l1 ⊔ l2)
mul-ℝ⁺ (x , is-pos-x) (y , is-pos-y) =
  (x *ℝ y , is-positive-mul-ℝ is-pos-x is-pos-y)

infixl 40 _*ℝ⁺_
_*ℝ⁺_ : {l1 l2 : Level} → ℝ⁺ l1 → ℝ⁺ l2 → ℝ⁺ (l1 ⊔ l2)
_*ℝ⁺_ = mul-ℝ⁺
```

## Properties

### Commutativity of multiplication of positive real numbers

```agda
abstract
  commutative-mul-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) → (x *ℝ⁺ y ＝ y *ℝ⁺ x)
  commutative-mul-ℝ⁺ x⁺@(x , _) y⁺@(y , _) =
    eq-ℝ⁺ (x⁺ *ℝ⁺ y⁺) (y⁺ *ℝ⁺ x⁺) (commutative-mul-ℝ x y)
```

### Multiplication by a positive real number preserves and reflects strict inequality

```agda
abstract
  preserves-le-left-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) (y : ℝ l2) (z : ℝ l3) → le-ℝ y z →
    le-ℝ (real-ℝ⁺ x *ℝ y) (real-ℝ⁺ x *ℝ z)
  preserves-le-left-mul-ℝ⁺ x⁺@(x , 0<x) y z y<z =
    le-is-positive-diff-ℝ
      ( tr
        ( is-positive-ℝ)
        ( left-distributive-mul-diff-ℝ x z y)
        ( is-positive-mul-ℝ 0<x (is-positive-diff-le-ℝ y<z)))

  reflects-le-left-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) (y : ℝ l2) (z : ℝ l3) →
    le-ℝ (real-ℝ⁺ x *ℝ y) (real-ℝ⁺ x *ℝ z) → le-ℝ y z
  reflects-le-left-mul-ℝ⁺ x y z xy<xz =
    preserves-le-sim-ℝ _ _ _ _
      ( cancel-left-div-mul-ℝ⁺ x y)
      ( cancel-left-div-mul-ℝ⁺ x z)
      ( preserves-le-left-mul-ℝ⁺ (inv-ℝ⁺ x) _ _ xy<xz)

  preserves-le-right-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) (y : ℝ l2) (z : ℝ l3) → le-ℝ y z →
    le-ℝ (y *ℝ real-ℝ⁺ x) (z *ℝ real-ℝ⁺ x)
  preserves-le-right-mul-ℝ⁺ x y z y<z =
    binary-tr
      ( le-ℝ)
      ( commutative-mul-ℝ _ _)
      ( commutative-mul-ℝ _ _)
      ( preserves-le-left-mul-ℝ⁺ x y z y<z)

  reflects-le-right-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) (y : ℝ l2) (z : ℝ l3) →
    le-ℝ (y *ℝ real-ℝ⁺ x) (z *ℝ real-ℝ⁺ x) → le-ℝ y z
  reflects-le-right-mul-ℝ⁺ x y z yx<zx =
    reflects-le-left-mul-ℝ⁺ x y z
      ( binary-tr
        ( le-ℝ)
        ( commutative-mul-ℝ _ _)
        ( commutative-mul-ℝ _ _)
        ( yx<zx))
```

### Multiplication by a positive real number preserves and reflects inequality

```agda
abstract
  preserves-leq-left-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) (y : ℝ l2) (z : ℝ l3) → leq-ℝ y z →
    leq-ℝ (real-ℝ⁺ x *ℝ y) (real-ℝ⁺ x *ℝ z)
  preserves-leq-left-mul-ℝ⁺ x⁺ = preserves-leq-left-mul-ℝ⁰⁺ (nonnegative-ℝ⁺ x⁺)

  preserves-leq-right-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) (y : ℝ l2) (z : ℝ l3) → leq-ℝ y z →
    leq-ℝ (y *ℝ real-ℝ⁺ x) (z *ℝ real-ℝ⁺ x)
  preserves-leq-right-mul-ℝ⁺ x⁺ =
    preserves-leq-right-mul-ℝ⁰⁺ (nonnegative-ℝ⁺ x⁺)

  reflects-leq-left-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) (y : ℝ l2) (z : ℝ l3) →
    leq-ℝ (real-ℝ⁺ x *ℝ y) (real-ℝ⁺ x *ℝ z) → leq-ℝ y z
  reflects-leq-left-mul-ℝ⁺ x y z xy≤xz =
    preserves-leq-sim-ℝ _ _ _ _
      ( cancel-left-div-mul-ℝ⁺ x y)
      ( cancel-left-div-mul-ℝ⁺ x z)
      ( preserves-leq-left-mul-ℝ⁺ (inv-ℝ⁺ x) _ _ xy≤xz)

  reflects-leq-right-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) (y : ℝ l2) (z : ℝ l3) →
    leq-ℝ (y *ℝ real-ℝ⁺ x) (z *ℝ real-ℝ⁺ x) → leq-ℝ y z
  reflects-leq-right-mul-ℝ⁺ x y z yx≤zx =
    reflects-leq-left-mul-ℝ⁺ x y z
      ( binary-tr
        ( leq-ℝ)
        ( commutative-mul-ℝ _ _)
        ( commutative-mul-ℝ _ _)
        ( yx≤zx))
```
