# Closed intervals of rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.closed-intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.action-on-identifications-functions
open import foundation.action-on-identifications-binary-functions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.identity-types
open import foundation.propositions
open import foundation.binary-transport
open import foundation.conjunction
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import order-theory.decidable-total-orders
open import elementary-number-theory.decidable-total-order-rational-numbers
open import foundation.universe-levels
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
```

</details>

## Idea

## Definition

```agda
module _
  (a b : ℚ)
  where

  closed-interval-ℚ : subtype lzero ℚ
  closed-interval-ℚ q = leq-ℚ-Prop a q ∧ leq-ℚ-Prop q b

  is-in-closed-interval-ℚ : ℚ → UU lzero
  is-in-closed-interval-ℚ q = type-Prop (closed-interval-ℚ q)

module _
  (a b : ℚ)
  where

  unordered-closed-interval-ℚ : subtype lzero ℚ
  unordered-closed-interval-ℚ = closed-interval-ℚ (min-ℚ a b) (max-ℚ a b)

  is-in-unordered-closed-interval-ℚ : ℚ → UU lzero
  is-in-unordered-closed-interval-ℚ q =
    type-Prop (unordered-closed-interval-ℚ q)
```

## Properties

```agda
abstract
  right-mul-closed-interval-ℚ :
    (a b p q : ℚ) → is-in-closed-interval-ℚ a b p →
    is-in-unordered-closed-interval-ℚ (a *ℚ q) (b *ℚ q) (p *ℚ q)
  right-mul-closed-interval-ℚ a b p q (a≤p , p≤b) =
    trichotomy-le-ℚ
      q
      zero-ℚ
      ( λ q<0 →
        let
          pos-neg-q = is-positive-le-zero-ℚ (neg-ℚ q) (neg-le-ℚ q zero-ℚ q<0)
          neg-q⁺ : ℚ⁺
          neg-q⁺ = neg-ℚ q , pos-neg-q
          leq-mul-negative : (x y : ℚ) → leq-ℚ x y → leq-ℚ (y *ℚ q) (x *ℚ q)
          leq-mul-negative x y x≤y =
            binary-tr
              ( leq-ℚ)
              ( ap neg-ℚ (right-negative-law-mul-ℚ y q) ∙ neg-neg-ℚ _)
              ( ap neg-ℚ (right-negative-law-mul-ℚ y q) ∙
          a-neg-q≤b-neg-q = preserves-leq-right-mul-ℚ⁺ neg-q⁺ a b a≤b
          a-neg-q≤p-neg-q = preserves-leq-right-mul-ℚ⁺ neg-q⁺ a p a≤p
          p-neg-q≤b-neg-q = preserves-leq-right-mul-ℚ⁺ neg-q⁺ p b p≤b
          bq≤aq : leq-ℚ (b *ℚ q) (a *ℚ q)
          bq≤aq =
            binary-tr
              ( leq-ℚ)
              ( ap neg-ℚ (right-negative-law-mul-ℚ b q) ∙ neg-neg-ℚ _)
              ( ap neg-ℚ (right-negative-law-mul-ℚ a q) ∙ neg-neg-ℚ _)
              ( neg-leq-ℚ (a *ℚ neg-ℚ q) (b *ℚ neg-ℚ q) a-neg-q≤b-neg-q)
          min=bq = right-leq-left-min-ℚ (a *ℚ q) (b *ℚ q) bq≤aq
          max=aq = right-leq-left-min-ℚ (a *ℚ q) (b *ℚ q) bq≤aq
          pq≤aq =
            binary-tr
              ( leq-ℚ)
              ( ap neg-ℚ (right-negative-law-mul-ℚ p q) ∙ neg-neg-ℚ _)
              ( ap neg-ℚ (right-negative-law-mul-ℚ a q) ∙ neg-neg-ℚ _)
              ( neg-leq-ℚ (a *ℚ neg-ℚ q) (p *ℚ neg-ℚ q) a-neg-q≤p-neg-q)
          aq≤pq =
        in {!   !})
      ( λ q=0 →
        let
          aq=0 = ap (a *ℚ_) q=0 ∙ right-zero-law-mul-ℚ a
          bq=0 = ap (b *ℚ_) q=0 ∙ right-zero-law-mul-ℚ b
          pq=0 = ap (p *ℚ_) q=0 ∙ right-zero-law-mul-ℚ p
          min=0 : min-ℚ (a *ℚ q) (b *ℚ q) ＝ zero-ℚ
          min=0 = ap-binary min-ℚ aq=0 bq=0 ∙ idempotent-min-ℚ zero-ℚ
          max=0 : max-ℚ (a *ℚ q) (b *ℚ q) ＝ zero-ℚ
          max=0 = ap-binary max-ℚ aq=0 bq=0 ∙ idempotent-max-ℚ zero-ℚ
        in
          leq-eq-ℚ (min-ℚ (a *ℚ q) (b *ℚ q)) (p *ℚ q) (min=0 ∙ inv pq=0) ,
          leq-eq-ℚ (p *ℚ q) (max-ℚ (a *ℚ q) (b *ℚ q)) (pq=0 ∙ inv max=0))
      ( λ 0<q →
        let
          pos-q = is-positive-le-zero-ℚ q 0<q
          q⁺ : ℚ⁺
          q⁺ = q , pos-q
          aq≤bq = preserves-leq-right-mul-ℚ⁺ q⁺ a b a≤b
        in
          inv-tr
            ( λ r → leq-ℚ r (p *ℚ q))
            ( left-leq-right-min-ℚ (a *ℚ q) (b *ℚ q) aq≤bq)
            ( preserves-leq-right-mul-ℚ⁺ q⁺ a p a≤p) ,
          inv-tr
            ( leq-ℚ (p *ℚ q))
            ( left-leq-right-max-ℚ (a *ℚ q) (b *ℚ q) aq≤bq)
            ( preserves-leq-right-mul-ℚ⁺ q⁺ p b p≤b))
    where
      a≤b : leq-ℚ a b
      a≤b = transitive-leq-ℚ a p b p≤b a≤p
```
