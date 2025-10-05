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

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.positive-real-numbers
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
