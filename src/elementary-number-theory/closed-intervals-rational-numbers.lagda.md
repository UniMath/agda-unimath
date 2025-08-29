# Closed intervals of rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.closed-intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.decidable-total-order-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.distance-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.ring-of-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import lists.tuples

open import order-theory.decidable-total-orders
open import order-theory.posets

open import reflection.group-solver
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

### Bound on the width of the interval produced by multiplying two intervals

```agda
abstract
  bound-width-mul-interval-ℚ :
    (a b c d : ℚ) →
    (a≤b : leq-ℚ a b) (c≤d : leq-ℚ c d) →
    max-ℚ (max-ℚ (a *ℚ c) (a *ℚ d)) (max-ℚ (b *ℚ c) (b *ℚ d)) -ℚ
    min-ℚ (min-ℚ (a *ℚ c) (a *ℚ d)) (min-ℚ (b *ℚ c) (b *ℚ d))
      ≤-ℚ
    (b -ℚ a) *ℚ max-ℚ (rational-abs-ℚ c) (rational-abs-ℚ d) +ℚ
    (d -ℚ c) *ℚ max-ℚ (rational-abs-ℚ a) (rational-abs-ℚ b)
  bound-width-mul-interval-ℚ a b c d a≤b c≤d =
    let
      ||_|| = rational-abs-ℚ
      <b-a><max|c||d|>⁰⁺ =
        mul-ℚ⁰⁺
          ( nonnegative-diff-leq-ℚ a b a≤b)
          ( max-ℚ⁰⁺ (abs-ℚ c) (abs-ℚ d))
      <b-a><max|c||d|> = rational-ℚ⁰⁺ <b-a><max|c||d|>⁰⁺
      <d-c><max|a||b|>⁰⁺ =
        mul-ℚ⁰⁺
          ( nonnegative-diff-leq-ℚ c d c≤d)
          ( max-ℚ⁰⁺ (abs-ℚ a) (abs-ℚ b))
      <d-c><max|a||b|> = rational-ℚ⁰⁺ <d-c><max|a||b|>⁰⁺
      good : ℚ → UU lzero
      good q = q ≤-ℚ ( <b-a><max|c||d|> +ℚ <d-c><max|a||b|>)
      good-|ac-ad| : good (|| (a *ℚ c) -ℚ (a *ℚ d) ||)
      good-|ac-ad| =
        calculate-in-Poset ℚ-Poset
        chain-of-inequalities
          || (a *ℚ c) -ℚ (a *ℚ d) ||
            ≤ (d -ℚ c) *ℚ || a ||
              by
                leq-eq-ℚ _ _
                  ( ap ||_|| (inv (left-distributive-mul-diff-ℚ a c d)) ∙
                    rational-abs-mul-ℚ _ _ ∙
                    ap-mul-ℚ refl (rational-dist-leq-ℚ c≤d) ∙
                    commutative-mul-ℚ _ _)
              in-Poset ℚ-Poset
            ≤ <d-c><max|a||b|>
              by
                preserves-leq-left-mul-ℚ⁰⁺
                  ( nonnegative-diff-leq-ℚ c d c≤d)
                  ( || a ||)
                  ( max-ℚ (|| a ||) (|| b ||))
                  ( leq-left-max-ℚ _ _)
              in-Poset ℚ-Poset
            ≤ <b-a><max|c||d|> +ℚ <d-c><max|a||b|>
              by is-inflationary-map-left-add-rational-ℚ⁰⁺ <b-a><max|c||d|>⁰⁺ _
              in-Poset ℚ-Poset
      good-|bc-bd| : good (|| (b *ℚ c) -ℚ (b *ℚ d) ||)
      good-|bc-bd| =
        calculate-in-Poset ℚ-Poset
        chain-of-inequalities
          || (b *ℚ c) -ℚ (b *ℚ d) ||
          ≤ (d -ℚ c) *ℚ || b ||
            by
              leq-eq-ℚ _ _
                ( ap ||_|| (inv (left-distributive-mul-diff-ℚ b c d)) ∙
                  rational-abs-mul-ℚ _ _ ∙
                  ap-mul-ℚ refl (rational-dist-leq-ℚ c≤d) ∙
                  commutative-mul-ℚ _ _)
            in-Poset ℚ-Poset
          ≤ <d-c><max|a||b|>
            by
              preserves-leq-left-mul-ℚ⁰⁺
                ( nonnegative-diff-leq-ℚ c d c≤d)
                ( || b ||)
                ( max-ℚ (|| a ||) (|| b ||))
                ( leq-right-max-ℚ _ _)
            in-Poset ℚ-Poset
          ≤ <b-a><max|c||d|> +ℚ <d-c><max|a||b|>
            by is-inflationary-map-left-add-rational-ℚ⁰⁺ <b-a><max|c||d|>⁰⁺ _
            in-Poset ℚ-Poset
      good-|ac-bc| : good (|| (a *ℚ c) -ℚ (b *ℚ c) ||)
      good-|ac-bc| =
        calculate-in-Poset ℚ-Poset
        chain-of-inequalities
          || (a *ℚ c) -ℚ (b *ℚ c) ||
          ≤ (b -ℚ a) *ℚ || c ||
            by
              leq-eq-ℚ _ _
                ( ap
                  ( rational-abs-ℚ)
                  ( inv (right-distributive-mul-diff-ℚ a b c)) ∙
                  rational-abs-mul-ℚ _ _ ∙
                  ap-mul-ℚ (rational-dist-leq-ℚ a≤b) refl)
            in-Poset ℚ-Poset
          ≤ (b -ℚ a) *ℚ max-ℚ (|| c ||) (|| d ||)
            by
              preserves-leq-left-mul-ℚ⁰⁺
                ( nonnegative-diff-leq-ℚ a b a≤b)
                ( || c ||)
                ( max-ℚ (|| c ||) (|| d ||))
                ( leq-left-max-ℚ _ _)
            in-Poset ℚ-Poset
          ≤ <b-a><max|c||d|> +ℚ <d-c><max|a||b|>
            by is-inflationary-map-right-add-rational-ℚ⁰⁺ <d-c><max|a||b|>⁰⁺ _
            in-Poset ℚ-Poset
      good-|ad-bd| : good (|| (a *ℚ d) -ℚ (b *ℚ d) ||)
      good-|ad-bd| =
        calculate-in-Poset ℚ-Poset
        chain-of-inequalities
          || (a *ℚ d) -ℚ (b *ℚ d) ||
          ≤ (b -ℚ a) *ℚ || d ||
            by
              leq-eq-ℚ _ _
                ( ap
                  ( rational-abs-ℚ)
                  ( inv (right-distributive-mul-diff-ℚ a b d)) ∙
                  rational-abs-mul-ℚ _ _ ∙
                  ap-mul-ℚ (rational-dist-leq-ℚ a≤b) refl)
            in-Poset ℚ-Poset
          ≤ (b -ℚ a) *ℚ max-ℚ (|| c ||) (|| d ||)
            by
              preserves-leq-left-mul-ℚ⁰⁺
                ( nonnegative-diff-leq-ℚ a b a≤b)
                ( || d ||)
                ( max-ℚ (|| c ||) (|| d ||))
                ( leq-right-max-ℚ _ _)
            in-Poset ℚ-Poset
          ≤ <b-a><max|c||d|> +ℚ <d-c><max|a||b|>
            by is-inflationary-map-right-add-rational-ℚ⁰⁺ <d-c><max|a||b|>⁰⁺ _
            in-Poset ℚ-Poset
      x : GroupSyntax 3
      x = inner (zero-Inductive-Fin)
      y : GroupSyntax 3
      y = inner (succ-Inductive-Fin zero-Inductive-Fin)
      z : GroupSyntax 3
      z = inner (succ-Inductive-Fin (succ-Inductive-Fin zero-Inductive-Fin))
      good-|ad-bc| : good (|| (a *ℚ d) -ℚ (b *ℚ c) ||)
      good-|ad-bc| =
        calculate-in-Poset ℚ-Poset
        chain-of-inequalities
          || (a *ℚ d) -ℚ (b *ℚ c) ||
          ≤ || (a *ℚ d -ℚ a *ℚ c) +ℚ (a *ℚ c -ℚ b *ℚ c) ||
            by
              leq-eq-ℚ _ _
                ( ap rational-abs-ℚ
                  ( inv
                    ( simplifyExpression
                      ( group-add-ℚ)
                      ( gMul (gMul x (gInv y)) (gMul y (gInv z)))
                      ( a *ℚ d ∷ a *ℚ c ∷ b *ℚ c ∷ empty-tuple))))
            in-Poset ℚ-Poset
          ≤ || a *ℚ (d -ℚ c) +ℚ (a -ℚ b) *ℚ c ||
            by
              leq-eq-ℚ _ _
                ( ap rational-abs-ℚ
                  ( inv
                    ( ap-add-ℚ
                      ( left-distributive-mul-diff-ℚ a d c)
                      ( right-distributive-mul-diff-ℚ a b c))))
            in-Poset ℚ-Poset
          ≤ (|| a *ℚ (d -ℚ c) ||) +ℚ (|| ( a -ℚ b) *ℚ c ||)
            by triangle-inequality-abs-ℚ _ _
            in-Poset ℚ-Poset
          ≤ ((b -ℚ a) *ℚ || c ||) +ℚ ((d -ℚ c) *ℚ || a ||)
            by
              leq-eq-ℚ _ _
                ( ap-add-ℚ
                  ( rational-abs-mul-ℚ _ _ ∙
                    ap-mul-ℚ refl (rational-dist-leq-reversed-ℚ c≤d) ∙
                    commutative-mul-ℚ _ _)
                  ( rational-abs-mul-ℚ _ _ ∙
                    ap-mul-ℚ (rational-dist-leq-ℚ a≤b) refl) ∙
                  commutative-add-ℚ _ _)
            in-Poset ℚ-Poset
          ≤ <b-a><max|c||d|> +ℚ <d-c><max|a||b|>
            by
              preserves-leq-add-ℚ
                ( preserves-leq-left-mul-ℚ⁰⁺
                  ( nonnegative-diff-leq-ℚ a b a≤b)
                  ( || c ||)
                  ( max-ℚ (|| c ||) (|| d ||))
                  ( leq-left-max-ℚ _ _))
                ( preserves-leq-left-mul-ℚ⁰⁺
                  ( nonnegative-diff-leq-ℚ c d c≤d)
                  ( || a ||)
                  ( max-ℚ (|| a ||) (|| b ||))
                  ( leq-left-max-ℚ _ _))
            in-Poset ℚ-Poset
      good-|ac-bd| : good (|| (a *ℚ c) -ℚ (b *ℚ d) ||)
      good-|ac-bd| =
        calculate-in-Poset ℚ-Poset
        chain-of-inequalities
          || (a *ℚ c) -ℚ (b *ℚ d) ||
          ≤ || (a *ℚ c -ℚ a *ℚ d) +ℚ (a *ℚ d -ℚ b *ℚ d) ||
            by
              leq-eq-ℚ _ _
                ( ap rational-abs-ℚ
                  ( inv
                    ( simplifyExpression
                      ( group-add-ℚ)
                      ( gMul (gMul x (gInv y)) (gMul y (gInv z)))
                      ( a *ℚ c ∷ a *ℚ d ∷ b *ℚ d ∷ empty-tuple))))
            in-Poset ℚ-Poset
          ≤ || a *ℚ (c -ℚ d) +ℚ (a -ℚ b) *ℚ d ||
            by
              leq-eq-ℚ _ _
                ( ap rational-abs-ℚ
                  ( inv
                    ( ap-add-ℚ
                      ( left-distributive-mul-diff-ℚ a c d)
                      ( right-distributive-mul-diff-ℚ a b d))))
            in-Poset ℚ-Poset
          ≤ (|| a *ℚ (c -ℚ d) ||) +ℚ (|| ( a -ℚ b) *ℚ d ||)
            by triangle-inequality-abs-ℚ _ _
            in-Poset ℚ-Poset
          ≤ ((b -ℚ a) *ℚ || d ||) +ℚ ((d -ℚ c) *ℚ || a ||)
            by
              leq-eq-ℚ _ _
                ( ap-add-ℚ
                  ( rational-abs-mul-ℚ _ _ ∙
                    ap-mul-ℚ refl (rational-dist-leq-ℚ c≤d) ∙
                    commutative-mul-ℚ _ _)
                  ( rational-abs-mul-ℚ _ _ ∙
                    ap-mul-ℚ (rational-dist-leq-ℚ a≤b) refl) ∙
                  commutative-add-ℚ _ _)
            in-Poset ℚ-Poset
          ≤ <b-a><max|c||d|> +ℚ <d-c><max|a||b|>
            by
              preserves-leq-add-ℚ
                ( preserves-leq-left-mul-ℚ⁰⁺
                  ( nonnegative-diff-leq-ℚ a b a≤b)
                  ( || d ||)
                  ( max-ℚ (|| c ||) (|| d ||))
                  ( leq-right-max-ℚ _ _))
                ( preserves-leq-left-mul-ℚ⁰⁺
                  ( nonnegative-diff-leq-ℚ c d c≤d)
                  ( || a ||)
                  ( max-ℚ (|| a ||) (|| b ||))
                  ( leq-left-max-ℚ _ _))
            in-Poset ℚ-Poset
      good-x-x : (x : ℚ) → good (|| x -ℚ x ||)
      good-x-x x =
        inv-tr good
          ( ap rational-abs-ℚ (right-inverse-law-add-ℚ x) ∙
            rational-abs-rational-ℚ⁰⁺ zero-ℚ⁰⁺)
          ( leq-zero-ℚ⁰⁺ (<b-a><max|c||d|>⁰⁺ +ℚ⁰⁺ <d-c><max|a||b|>⁰⁺))
      linear-leq p q = (leq-ℚ p q + leq-ℚ q p)
      max-ac-ad-bc-bd =
        max-ℚ (max-ℚ (a *ℚ c) (a *ℚ d)) (max-ℚ (b *ℚ c) (b *ℚ d))
      min-ac-ad-bc-bd =
        min-ℚ (min-ℚ (a *ℚ c) (a *ℚ d)) (min-ℚ (b *ℚ c) (b *ℚ d))
      motive =
        good (max-ac-ad-bc-bd -ℚ min-ac-ad-bc-bd)
      case-1 :
        {p q : ℚ} → max-ac-ad-bc-bd ＝ p → min-ac-ad-bc-bd ＝ q →
        good (|| p -ℚ q ||) →
        motive
      case-1 {p} {q} max=p min=q good-|p-q| =
        transitive-leq-ℚ
          ( max-ac-ad-bc-bd -ℚ min-ac-ad-bc-bd)
          ( || max-ac-ad-bc-bd -ℚ min-ac-ad-bc-bd ||)
          ( <b-a><max|c||d|> +ℚ <d-c><max|a||b|>)
          ( inv-tr good
            ( ap rational-abs-ℚ (ap-diff-ℚ max=p min=q))
            ( good-|p-q|))
          ( leq-abs-ℚ _)
      case-2 :
        {p q : ℚ} → max-ac-ad-bc-bd ＝ p → min-ac-ad-bc-bd ＝ q →
        good (|| q -ℚ p ||) → motive
      case-2 max=p min=q good-|q-p| =
        case-1 max=p min=q
          ( tr good (commutative-rational-dist-ℚ _ _) good-|q-p|)
      casework :
        ( ( ( max-ac-ad-bc-bd ＝ a *ℚ c) +
            ( max-ac-ad-bc-bd ＝ a *ℚ d)) +
          ( ( max-ac-ad-bc-bd ＝ b *ℚ c) +
            ( max-ac-ad-bc-bd ＝ b *ℚ d))) →
        ( ( ( min-ac-ad-bc-bd ＝ a *ℚ c) +
            ( min-ac-ad-bc-bd ＝ a *ℚ d)) +
          ( ( min-ac-ad-bc-bd ＝ b *ℚ c) +
            ( min-ac-ad-bc-bd ＝ b *ℚ d))) →
        motive
      casework = λ where
        (inl (inl max=ac)) (inl (inl min=ac)) →
          case-1 max=ac min=ac (good-x-x (a *ℚ c))
        (inl (inl max=ac)) (inl (inr min=ad)) →
          case-1 max=ac min=ad good-|ac-ad|
        (inl (inl max=ac)) (inr (inl min=bc)) →
          case-1 max=ac min=bc good-|ac-bc|
        (inl (inl max=ac)) (inr (inr min=bd)) →
          case-1 max=ac min=bd good-|ac-bd|
        (inl (inr max=ad)) (inl (inl min=ac)) →
          case-2 max=ad min=ac good-|ac-ad|
        (inl (inr max=ad)) (inl (inr min=ad)) →
          case-1 max=ad min=ad (good-x-x (a *ℚ d))
        (inl (inr max=ad)) (inr (inl min=bc)) →
          case-1 max=ad min=bc good-|ad-bc|
        (inl (inr max=ad)) (inr (inr min=bd)) →
          case-1 max=ad min=bd good-|ad-bd|
        (inr (inl max=bc)) (inl (inl min=ac)) →
          case-2 max=bc min=ac good-|ac-bc|
        (inr (inl max=bc)) (inl (inr min=ad)) →
          case-2 max=bc min=ad good-|ad-bc|
        (inr (inl max=bc)) (inr (inl min=bc)) →
          case-1 max=bc min=bc (good-x-x (b *ℚ c))
        (inr (inl max=bc)) (inr (inr min=bd)) →
          case-1 max=bc min=bd good-|bc-bd|
        (inr (inr max=bd)) (inl (inl min=ac)) →
          case-2 max=bd min=ac good-|ac-bd|
        (inr (inr max=bd)) (inl (inr min=ad)) →
          case-2 max=bd min=ad good-|ad-bd|
        (inr (inr max=bd)) (inr (inl min=bc)) →
          case-2 max=bd min=bc good-|bc-bd|
        (inr (inr max=bd)) (inr (inr min=bd)) →
          case-1 max=bd min=bd (good-x-x (b *ℚ d))
    in
      casework
        ( max-eq-one-of-four-Decidable-Total-Order
          ( ℚ-Decidable-Total-Order)
          ( a *ℚ c)
          ( a *ℚ d)
          ( b *ℚ c)
          ( b *ℚ d))
        ( min-eq-one-of-four-Decidable-Total-Order
          ( ℚ-Decidable-Total-Order)
          ( a *ℚ c)
          ( a *ℚ d)
          ( b *ℚ c)
          ( b *ℚ d))
```
