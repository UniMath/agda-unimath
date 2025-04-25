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
open import elementary-number-theory.positive-and-negative-rational-numbers
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
{{#concept "closed interval" Disambiguation="rational numbers" WDID=Q78240777 WD="closed interval" Agda=closed-interval-ℚ}}
`[q , r]` if `q` is
[less than or equal to](elementary-number-theory.inequality-rational-numbers.md)
`p` and `p` is less than or equal to `r`.

## Definition

```agda
module _
  (p q : ℚ)
  where

  closed-interval-ℚ : subtype lzero ℚ
  closed-interval-ℚ r = (leq-ℚ-Prop p r) ∧ (leq-ℚ-Prop r q)

  is-in-closed-interval-ℚ : ℚ → UU lzero
  is-in-closed-interval-ℚ r = type-Prop (closed-interval-ℚ r)

unordered-closed-interval-ℚ : ℚ → ℚ → subtype lzero ℚ
unordered-closed-interval-ℚ p q = closed-interval-ℚ (min-ℚ p q) (max-ℚ p q)

is-in-unordered-closed-interval-ℚ : ℚ → ℚ → ℚ → UU lzero
is-in-unordered-closed-interval-ℚ p q =
  is-in-closed-interval-ℚ (min-ℚ p q) (max-ℚ p q)

is-in-unordered-closed-interval-is-in-closed-interval-ℚ :
  (p q r : ℚ) →
  is-in-closed-interval-ℚ p q r →
  is-in-unordered-closed-interval-ℚ p q r
is-in-unordered-closed-interval-is-in-closed-interval-ℚ p q r (p≤r , q≤r) =
  transitive-leq-ℚ
    ( min-ℚ p q)
    ( p)
    ( r)
    ( p≤r)
    ( leq-left-min-ℚ p q) ,
  transitive-leq-ℚ
    ( r)
    ( q)
    ( max-ℚ p q)
    ( leq-right-max-ℚ p q)
    ( q≤r)

is-in-reversed-unordered-closed-interval-is-in-closed-interval-ℚ :
  (p q r : ℚ) → is-in-closed-interval-ℚ p q r →
  is-in-unordered-closed-interval-ℚ q p r
is-in-reversed-unordered-closed-interval-is-in-closed-interval-ℚ
  p q r (p≤r , q≤r) =
  transitive-leq-ℚ
    ( min-ℚ q p)
    ( p)
    ( r)
    ( p≤r)
    ( leq-right-min-ℚ q p) ,
  transitive-leq-ℚ
    ( r)
    ( q)
    ( max-ℚ q p)
    ( leq-left-max-ℚ q p)
    ( q≤r)
```

## Properties

### Multiplication of elements in a closed interval

```agda
abstract
  left-mul-negative-closed-interval-ℚ :
    (p q r s : ℚ) →
    is-in-closed-interval-ℚ p q r → is-negative-ℚ s →
    is-in-closed-interval-ℚ (q *ℚ s) (p *ℚ s) (r *ℚ s)
  left-mul-negative-closed-interval-ℚ p q r s (p≤r , r≤q) neg-s =
    let
      s⁻ = s , neg-s
    in
      reverses-leq-right-mul-ℚ⁻ s⁻ r q r≤q ,
      reverses-leq-right-mul-ℚ⁻ s⁻ p r p≤r

  left-mul-positive-closed-interval-ℚ :
    (p q r s : ℚ) →
    is-in-closed-interval-ℚ p q r → is-positive-ℚ s →
    is-in-closed-interval-ℚ (p *ℚ s) (q *ℚ s) (r *ℚ s)
  left-mul-positive-closed-interval-ℚ p q r s (p≤r , r≤q) pos-s =
    let
      s⁺ = s , pos-s
    in
      preserves-leq-right-mul-ℚ⁺ s⁺ p r p≤r ,
      preserves-leq-right-mul-ℚ⁺ s⁺ r q r≤q

  left-mul-closed-interval-ℚ :
    (p q r s : ℚ) →
    is-in-closed-interval-ℚ p q r →
    is-in-unordered-closed-interval-ℚ (p *ℚ s) (q *ℚ s) (r *ℚ s)
  left-mul-closed-interval-ℚ p q r s H@(p≤r , r≤q) =
    let
      p≤q = transitive-leq-ℚ p r q r≤q p≤r
    in
      trichotomy-sign-ℚ
        ( s)
        ( λ neg-s →
          is-in-reversed-unordered-closed-interval-is-in-closed-interval-ℚ
            (q *ℚ s)
            (p *ℚ s)
            (r *ℚ s)
            ( left-mul-negative-closed-interval-ℚ p q r s H neg-s))
        ( λ s=0 →
          let
            ps=0 = ap (p *ℚ_) s=0 ∙ right-zero-law-mul-ℚ p
            rs=0 = ap (r *ℚ_) s=0 ∙ right-zero-law-mul-ℚ r
            qs=0 = ap (q *ℚ_) s=0 ∙ right-zero-law-mul-ℚ q
          in
            leq-eq-ℚ
              ( _)
              ( _)
              ( ap-binary min-ℚ ps=0 qs=0 ∙
                idempotent-min-ℚ zero-ℚ ∙ inv rs=0) ,
            leq-eq-ℚ
              ( _)
              ( _)
              ( rs=0 ∙
                inv (ap-binary max-ℚ ps=0 qs=0 ∙ idempotent-max-ℚ zero-ℚ)))
        ( λ pos-s →
          is-in-unordered-closed-interval-is-in-closed-interval-ℚ
            ( p *ℚ s)
            ( q *ℚ s)
            ( r *ℚ s)
            ( left-mul-positive-closed-interval-ℚ p q r s H pos-s))

abstract
  right-mul-closed-interval-ℚ :
    (p q r s : ℚ) →
    is-in-closed-interval-ℚ p q r →
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

abstract
  mul-closed-interval-closed-interval-ℚ :
    (p q r s t u : ℚ) →
    is-in-closed-interval-ℚ p q r →
    is-in-closed-interval-ℚ s t u →
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
    in
      transitive-leq-ℚ
        ( min-ℚ (min-ℚ (p *ℚ s) (p *ℚ t)) (min-ℚ (q *ℚ s) (q *ℚ t)))
        ( min-ℚ (p *ℚ u) (q *ℚ u))
        ( r *ℚ u)
        ( min-pu-qu≤ru)
        ( min-leq-leq-ℚ
          ( min-ℚ (p *ℚ s) (p *ℚ t))
          ( p *ℚ u)
          ( min-ℚ (q *ℚ s) (q *ℚ t))
          ( q *ℚ u)
          ( min-ps-pt≤pu)
          ( min-qs-qt≤qu)) ,
      transitive-leq-ℚ
        ( r *ℚ u)
        ( max-ℚ (p *ℚ u) (q *ℚ u))
        ( max-ℚ (max-ℚ (p *ℚ s) (p *ℚ t)) (max-ℚ (q *ℚ s) (q *ℚ t)))
        ( max-leq-leq-ℚ
          ( p *ℚ u)
          ( max-ℚ (p *ℚ s) (p *ℚ t))
          ( q *ℚ u)
          ( max-ℚ (q *ℚ s) (q *ℚ t))
          ( pu≤max-ps-pt)
          ( qu≤max-qs-qt))
        ( ru≤max-pu-qu)
```
