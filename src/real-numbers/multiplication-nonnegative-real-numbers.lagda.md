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
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
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
opaque
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
            b⁺ = (b , is-positive-is-in-upper-cut-ℝ⁰⁺ (x , 0≤x) b x<b)
            d⁺ = (d , is-positive-is-in-upper-cut-ℝ⁰⁺ (y , 0≤y) d y<d)
          is-positive-le-ℚ⁺
            ( b⁺ *ℚ⁺ d⁺)
            ( q)
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
