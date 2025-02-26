# Closed intervals of rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.closed-intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

A [rational number](elementary-number-theory.rational-numbers.md) `p` is in a
{{#concept "closed interval" Disambiguation="rational numbers" WDID=Q78240777 WD="closed interval"}}
`[q , r]` if `q` is
[less than or equal to](elementary-number-theory.inequality-rational-numbers.md)
`p` and `p` is less than or equal to `r`.

## Definition

```agda
module _
  (p q : ℚ)
  where

  closed-interval-ℚ : subtype lzero ℚ
  closed-interval-ℚ r = leq-ℚ-Prop p r ∧ leq-ℚ-Prop r q

  is-in-closed-interval-ℚ : ℚ → UU lzero
  is-in-closed-interval-ℚ r = type-Prop (closed-interval-ℚ r)

unordered-closed-interval-ℚ : ℚ → ℚ → subtype lzero ℚ
unordered-closed-interval-ℚ p q = closed-interval-ℚ (min-ℚ p q) (max-ℚ p q)

is-in-unordered-closed-interval-ℚ : ℚ → ℚ → ℚ → UU lzero
is-in-unordered-closed-interval-ℚ p q =
  is-in-closed-interval-ℚ (min-ℚ p q) (max-ℚ p q)
```

## Properties

### Multiplication of elements in a closed interval

```agda
abstract
  left-mul-closed-interval-ℚ : (p q r s : ℚ) → is-in-closed-interval-ℚ p q r →
    is-in-unordered-closed-interval-ℚ (p *ℚ s) (q *ℚ s) (r *ℚ s)
  left-mul-closed-interval-ℚ p q r s (p≤r , r≤q) =
    let
      p≤q = transitive-leq-ℚ p r q r≤q p≤r
    in
      trichotomy-le-ℚ
        ( s)
        ( zero-ℚ)
        ( λ s<0 →
          let
            s⁻ = s , is-negative-le-zero-ℚ s s<0
            rs≤ps = reverses-leq-right-mul-ℚ⁻ s⁻ p r p≤r
            qs≤ps = reverses-leq-right-mul-ℚ⁻ s⁻ p q p≤q
            qs≤rs = reverses-leq-right-mul-ℚ⁻ s⁻ r q r≤q
            min=qs = right-leq-left-min-ℚ (p *ℚ s) (q *ℚ s) qs≤ps
            max=ps = right-leq-left-max-ℚ (p *ℚ s) (q *ℚ s) qs≤ps
          in
            inv-tr (λ t → leq-ℚ t (r *ℚ s)) min=qs qs≤rs ,
            inv-tr (leq-ℚ (r *ℚ s)) max=ps rs≤ps)
        ( λ s=0 →
          let
            ps=0 = ap (p *ℚ_) s=0 ∙ right-zero-law-mul-ℚ p
            rs=0 = ap (r *ℚ_) s=0 ∙ right-zero-law-mul-ℚ r
            qs=0 = ap (q *ℚ_) s=0 ∙ right-zero-law-mul-ℚ q
            min=0 = ap-binary min-ℚ ps=0 qs=0 ∙ idempotent-min-ℚ zero-ℚ
            max=0 = ap-binary max-ℚ ps=0 qs=0 ∙ idempotent-max-ℚ zero-ℚ
          in leq-eq-ℚ _ _ (min=0 ∙ inv rs=0) , leq-eq-ℚ _ _ (rs=0 ∙ inv max=0))
        ( λ 0<s →
          let
            s⁺ = s , is-positive-le-zero-ℚ s 0<s
            ps≤rs = preserves-leq-right-mul-ℚ⁺ s⁺ p r p≤r
            ps≤qs = preserves-leq-right-mul-ℚ⁺ s⁺ p q p≤q
            rs≤qs = preserves-leq-right-mul-ℚ⁺ s⁺ r q r≤q
            min=ps = left-leq-right-min-ℚ (p *ℚ s) (q *ℚ s) ps≤qs
            max=qs = left-leq-right-max-ℚ (p *ℚ s) (q *ℚ s) ps≤qs
          in
            inv-tr (λ t → leq-ℚ t (r *ℚ s)) min=ps ps≤rs ,
            inv-tr (leq-ℚ (r *ℚ s)) max=qs rs≤qs)

  right-mul-closed-interval-ℚ :
    (p q r s : ℚ) → is-in-closed-interval-ℚ p q r →
    is-in-unordered-closed-interval-ℚ (s *ℚ p) (s *ℚ q) (s *ℚ r)
  right-mul-closed-interval-ℚ p q r s r∈[p,q] =
    tr
      ( is-in-unordered-closed-interval-ℚ (s *ℚ p) (s *ℚ q))
      ( commutative-mul-ℚ r s)
      ( binary-tr
        ( λ a b → is-in-unordered-closed-interval-ℚ a b (r *ℚ s))
        ( commutative-mul-ℚ p s)
        ( commutative-mul-ℚ q s)
        ( left-mul-closed-interval-ℚ p q r s r∈[p,q]))

  mul-closed-interval-closed-interval-ℚ :
    (p q r s t u : ℚ) →
    is-in-closed-interval-ℚ p q r → is-in-closed-interval-ℚ s t u →
    is-in-closed-interval-ℚ
      (min-ℚ (min-ℚ (p *ℚ s) (p *ℚ t)) (min-ℚ (q *ℚ s) (q *ℚ t)))
      (max-ℚ (max-ℚ (p *ℚ s) (p *ℚ t)) (max-ℚ (q *ℚ s) (q *ℚ t)))
      (r *ℚ u)
  mul-closed-interval-closed-interval-ℚ p q r s t u r∈[p,q] u∈[s,t] =
    let
      (min-pu-qu≤ru , ru≤max-pu-qu) = left-mul-closed-interval-ℚ p q r u r∈[p,q]
      (min-ps-pt≤pu , pu≤max-ps-pt) =
        right-mul-closed-interval-ℚ s t u p u∈[s,t]
      (min-qs-qt≤qu , qu≤max-qs-qt) =
        right-mul-closed-interval-ℚ s t u q u∈[s,t]
      max-pu-qu≤max-max-ps-pt-max-qs-qt =
        max-leq-leq-ℚ
          ( p *ℚ u)
          ( max-ℚ (p *ℚ s) (p *ℚ t))
          ( q *ℚ u)
          ( max-ℚ (q *ℚ s) (q *ℚ t))
          ( pu≤max-ps-pt)
          ( qu≤max-qs-qt)
      ru≤max-max-ps-pt-max-qs-qt =
        transitive-leq-ℚ
          ( r *ℚ u)
          ( max-ℚ (p *ℚ u) (q *ℚ u))
          ( max-ℚ (max-ℚ (p *ℚ s) (p *ℚ t)) (max-ℚ (q *ℚ s) (q *ℚ t)))
          ( max-pu-qu≤max-max-ps-pt-max-qs-qt)
          ( ru≤max-pu-qu)
      min-min-ps-pt-min-qs-qt≤min-pu-qu =
        min-leq-leq-ℚ
          ( min-ℚ (p *ℚ s) (p *ℚ t))
          ( p *ℚ u)
          ( min-ℚ (q *ℚ s) (q *ℚ t))
          ( q *ℚ u)
          ( min-ps-pt≤pu)
          ( min-qs-qt≤qu)
      min-min-ps-pt-min-qs-qt≤ru =
        transitive-leq-ℚ
          ( min-ℚ (min-ℚ (p *ℚ s) (p *ℚ t)) (min-ℚ (q *ℚ s) (q *ℚ t)))
          ( min-ℚ (p *ℚ u) (q *ℚ u))
          ( r *ℚ u)
          min-pu-qu≤ru
          min-min-ps-pt-min-qs-qt≤min-pu-qu
    in min-min-ps-pt-min-qs-qt≤ru , ru≤max-max-ps-pt-max-qs-qt
```
