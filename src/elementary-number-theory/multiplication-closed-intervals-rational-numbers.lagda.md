# Multiplication on closed intervals in the rational numbers

```agda
module elementary-number-theory.multiplication-closed-intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-closed-intervals-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.closed-intervals-rational-numbers
open import elementary-number-theory.decidable-total-order-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.interior-closed-intervals-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.minima-and-maxima-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.multiplication-nonnegative-rational-numbers
open import elementary-number-theory.multiplication-positive-and-negative-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.multiplicative-group-of-rational-numbers
open import elementary-number-theory.multiplicative-monoid-of-rational-numbers
open import elementary-number-theory.negation-closed-intervals-rational-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.nonpositive-rational-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.images-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.minkowski-multiplication-commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups

open import order-theory.closed-intervals-total-orders
open import order-theory.decidable-total-orders
open import order-theory.total-orders
```

</details>

## Idea

Given two
[closed intervals](elementary-number-theory.closed-intervals-rational-numbers.md)
`[a, b]` and `[c, d]` in the
[rational numbers](elementary-number-theory.rational-numbers.md), the
[Minkowski product](group-theory.minkowski-multiplication-commutative-monoids.md)
of those intervals (interpreted as [subtypes](foundation.subtypes.md) of `ℚ`)
agrees with the interval `[min(ac, ad, bc, bd), max(ac, ad, bc, bd)]`.

Notably, this is because nonzero rational numbers are
[invertible](elementary-number-theory.multiplicative-group-of-rational-numbers.md);
this would not be true for the
[natural numbers](elementary-number-theory.natural-numbers.md), as
`[2, 2] * [a, b]` in the natural numbers is not the full interval `[2a, 2b]` but
only the even elements.

## Definition

```agda
mul-closed-interval-ℚ-ℚ :
  ℚ → closed-interval-ℚ → closed-interval-ℚ
mul-closed-interval-ℚ-ℚ a ((b , c) , _) =
  unordered-closed-interval-ℚ (a *ℚ b) (a *ℚ c)

mul-ℚ-closed-interval-ℚ :
  closed-interval-ℚ → ℚ → closed-interval-ℚ
mul-ℚ-closed-interval-ℚ ((a , b) , _) c =
  unordered-closed-interval-ℚ (a *ℚ c) (b *ℚ c)

mul-closed-interval-ℚ :
  closed-interval-ℚ → closed-interval-ℚ →
  closed-interval-ℚ
mul-closed-interval-ℚ ((a , b) , _) ((c , d) , _) =
  minimal-closed-interval-cover-of-four-elements-Total-Order
    ( ℚ-Total-Order)
    ( a *ℚ c)
    ( a *ℚ d)
    ( b *ℚ c)
    ( b *ℚ d)

lower-bound-mul-closed-interval-ℚ :
  closed-interval-ℚ → closed-interval-ℚ → ℚ
lower-bound-mul-closed-interval-ℚ [a,b] [c,d] =
  lower-bound-closed-interval-ℚ
    ( mul-closed-interval-ℚ [a,b] [c,d])

upper-bound-mul-closed-interval-ℚ :
  closed-interval-ℚ → closed-interval-ℚ → ℚ
upper-bound-mul-closed-interval-ℚ [a,b] [c,d] =
  upper-bound-closed-interval-ℚ
    ( mul-closed-interval-ℚ [a,b] [c,d])
```

## Properties

### Multiplication of an interval by a rational number

#### Multiplication of an interval by a negative rational number

```agda
mul-closed-interval-ℚ-ℚ⁻ :
  closed-interval-ℚ → ℚ⁻ → closed-interval-ℚ
mul-closed-interval-ℚ-ℚ⁻ ((p , q) , p≤q) s⁻@(s , _) =
  ((q *ℚ s , p *ℚ s) , reverses-leq-right-mul-ℚ⁻ s⁻ _ _ p≤q)

abstract
  mul-is-in-closed-interval-ℚ-ℚ⁻ :
    ([p,q] : closed-interval-ℚ) (r : ℚ⁻) (s : ℚ) →
    is-in-closed-interval-ℚ [p,q] s →
    is-in-closed-interval-ℚ
      ( mul-closed-interval-ℚ-ℚ⁻ [p,q] r)
      ( s *ℚ rational-ℚ⁻ r)
  mul-is-in-closed-interval-ℚ-ℚ⁻
    ((p , q) , p≤q) r s (p≤s , s≤q) =
      ( reverses-leq-right-mul-ℚ⁻ r _ _ s≤q ,
        reverses-leq-right-mul-ℚ⁻ r _ _ p≤s)

  is-in-im-is-in-mul-closed-interval-ℚ-ℚ⁻ :
    ([p,q] : closed-interval-ℚ) (r : ℚ⁻) (s : ℚ) →
    is-in-closed-interval-ℚ
      ( mul-closed-interval-ℚ-ℚ⁻ [p,q] r)
      ( s) →
    is-in-im-subtype
      ( mul-ℚ' (rational-ℚ⁻ r))
      ( subtype-closed-interval-ℚ [p,q])
      ( s)
  is-in-im-is-in-mul-closed-interval-ℚ-ℚ⁻
    ((p , q) , p≤q) r⁻@(r , _) s (qr≤s , s≤pr) =
      let r⁻¹ = inv-ℚ⁻ r⁻
      in
        intro-exists
          ( ( s *ℚ rational-ℚ⁻ r⁻¹ ,
              tr
                ( λ x → leq-ℚ x (s *ℚ rational-ℚ⁻ r⁻¹))
                ( associative-mul-ℚ _ _ _ ∙
                  ap-mul-ℚ refl (right-inverse-law-mul-ℚ⁻ r⁻) ∙
                  right-unit-law-mul-ℚ p)
                ( reverses-leq-right-mul-ℚ⁻ r⁻¹ s (p *ℚ r) s≤pr) ,
              tr
                ( leq-ℚ (s *ℚ rational-ℚ⁻ r⁻¹))
                ( associative-mul-ℚ _ _ _ ∙
                  ap-mul-ℚ refl (right-inverse-law-mul-ℚ⁻ r⁻) ∙
                  right-unit-law-mul-ℚ q)
                ( reverses-leq-right-mul-ℚ⁻ r⁻¹ (q *ℚ r) s qr≤s)))
          ( associative-mul-ℚ _ _ _ ∙
            ap-mul-ℚ refl (left-inverse-law-mul-ℚ⁻ r⁻) ∙
            right-unit-law-mul-ℚ s)

  is-closed-interval-map-mul-ℚ⁻ :
    (q : ℚ⁻) ([a,b] : closed-interval-ℚ) →
    is-closed-interval-map-ℚ
      ( mul-ℚ' (rational-ℚ⁻ q))
      ( [a,b])
      ( mul-closed-interval-ℚ-ℚ⁻ [a,b] q)
  is-closed-interval-map-mul-ℚ⁻ q [a,b] =
    ( ind-Σ (mul-is-in-closed-interval-ℚ-ℚ⁻ [a,b] q) ,
      ind-Σ (is-in-im-is-in-mul-closed-interval-ℚ-ℚ⁻ [a,b] q))
```

#### Multiplication of an interval by a positive rational number

```agda
mul-ℚ⁺-closed-interval-ℚ :
  closed-interval-ℚ → ℚ⁺ → closed-interval-ℚ
mul-ℚ⁺-closed-interval-ℚ ((p , q) , p≤q) s⁺@(s , _) =
  ((p *ℚ s , q *ℚ s) , preserves-leq-right-mul-ℚ⁺ s⁺ _ _ p≤q)

abstract
  mul-is-in-closed-interval-ℚ-ℚ⁺ :
    ([p,q] : closed-interval-ℚ) (r : ℚ⁺) (s : ℚ) →
    is-in-closed-interval-ℚ [p,q] s →
    is-in-closed-interval-ℚ
      ( mul-ℚ⁺-closed-interval-ℚ [p,q] r)
      ( s *ℚ rational-ℚ⁺ r)
  mul-is-in-closed-interval-ℚ-ℚ⁺
    ((p , q) , p≤q) r s (p≤s , s≤q) =
      ( preserves-leq-right-mul-ℚ⁺ r _ _ p≤s ,
        preserves-leq-right-mul-ℚ⁺ r _ _ s≤q)

  is-in-im-is-in-mul-ℚ⁺-closed-interval-ℚ :
    ([p,q] : closed-interval-ℚ) → (r : ℚ⁺) → (s : ℚ) →
    is-in-closed-interval-ℚ
      ( mul-ℚ⁺-closed-interval-ℚ [p,q] r)
      ( s) →
    is-in-im-subtype
      ( mul-ℚ' (rational-ℚ⁺ r))
      ( subtype-closed-interval-ℚ [p,q])
      ( s)
  is-in-im-is-in-mul-ℚ⁺-closed-interval-ℚ
    ((p , q) , p≤q) r⁺@(r , _) s (pr≤s , s≤qr) =
      let r⁻¹ = inv-ℚ⁺ r⁺
      in
        intro-exists
          ( ( s *ℚ rational-ℚ⁺ r⁻¹ ,
              tr
                ( λ x → leq-ℚ x (s *ℚ rational-ℚ⁺ r⁻¹))
                ( associative-mul-ℚ _ _ _ ∙
                  ap-mul-ℚ refl (ap rational-ℚ⁺ (right-inverse-law-mul-ℚ⁺ r⁺)) ∙
                  right-unit-law-mul-ℚ p)
                ( preserves-leq-right-mul-ℚ⁺ r⁻¹ (p *ℚ r) s pr≤s) ,
              tr
                ( leq-ℚ (s *ℚ rational-ℚ⁺ r⁻¹))
                ( associative-mul-ℚ _ _ _ ∙
                  ap-mul-ℚ refl (ap rational-ℚ⁺ (right-inverse-law-mul-ℚ⁺ r⁺)) ∙
                  right-unit-law-mul-ℚ q)
                ( preserves-leq-right-mul-ℚ⁺ r⁻¹ s (q *ℚ r) s≤qr)))
          ( associative-mul-ℚ _ _ _ ∙
            ap-mul-ℚ refl (ap rational-ℚ⁺ (left-inverse-law-mul-ℚ⁺ r⁺)) ∙
            right-unit-law-mul-ℚ s)

  is-closed-interval-map-left-mul-ℚ⁺ :
    (q : ℚ⁺) ([a,b] : closed-interval-ℚ) →
    is-closed-interval-map-ℚ
      ( mul-ℚ' (rational-ℚ⁺ q))
      ( [a,b])
      ( mul-ℚ⁺-closed-interval-ℚ [a,b] q)
  is-closed-interval-map-left-mul-ℚ⁺ q [a,b] =
    ( ind-Σ (mul-is-in-closed-interval-ℚ-ℚ⁺ [a,b] q) ,
      ind-Σ (is-in-im-is-in-mul-ℚ⁺-closed-interval-ℚ [a,b] q))
```

#### Multiplication of an interval by zero

```agda
abstract
  is-in-im-mul-is-in-zero-zero-closed-interval-ℚ :
    ([p,q] : closed-interval-ℚ) → (s : ℚ) →
    is-in-closed-interval-ℚ
      ( zero-zero-closed-interval-ℚ)
      ( s) →
    is-in-im-subtype
      ( mul-ℚ' zero-ℚ)
      ( subtype-closed-interval-ℚ [p,q])
      ( s)
  is-in-im-mul-is-in-zero-zero-closed-interval-ℚ
    ((p , q) , p≤q) s (0≤s , s≤0) =
      intro-exists
        ( p , refl-leq-ℚ p , p≤q)
        ( right-zero-law-mul-ℚ p ∙ antisymmetric-leq-ℚ _ _ 0≤s s≤0)

  is-closed-interval-map-mul-zero-ℚ :
    ([a,b] : closed-interval-ℚ) →
    is-closed-interval-map-ℚ
      ( mul-ℚ' zero-ℚ)
      ( [a,b])
      ( zero-zero-closed-interval-ℚ)
  is-closed-interval-map-mul-zero-ℚ [a,b] =
    ( ( λ r →
        inv-tr
          ( is-in-closed-interval-ℚ
            ( zero-zero-closed-interval-ℚ))
          ( right-zero-law-mul-ℚ _)
          ( refl-leq-ℚ zero-ℚ , refl-leq-ℚ zero-ℚ)) ,
      ind-Σ (is-in-im-mul-is-in-zero-zero-closed-interval-ℚ [a,b]))
```

#### Multiplication of an interval by any rational number

```agda
abstract
  mul-is-negative-ℚ-closed-interval-ℚ :
    ([p,q] : closed-interval-ℚ) (r : ℚ) (neg-r : is-negative-ℚ r) →
    mul-ℚ-closed-interval-ℚ [p,q] r ＝
    mul-closed-interval-ℚ-ℚ⁻ [p,q] (r , neg-r)
  mul-is-negative-ℚ-closed-interval-ℚ [p,q]@((p , q) , p≤q) r neg-r =
    unordered-closed-interval-leq-ℚ' _ _
      ( reverses-leq-right-mul-ℚ⁻ (r , neg-r) _ _ p≤q)

  mul-is-positive-ℚ-closed-interval-ℚ :
    ([p,q] : closed-interval-ℚ) (r : ℚ) (pos-r : is-positive-ℚ r) →
    mul-ℚ-closed-interval-ℚ [p,q] r ＝
    mul-ℚ⁺-closed-interval-ℚ [p,q] (r , pos-r)
  mul-is-positive-ℚ-closed-interval-ℚ [p,q]@((p , q) , p≤q) r pos-r =
    unordered-closed-interval-leq-ℚ _ _
      ( preserves-leq-right-mul-ℚ⁺ (r , pos-r) _ _ p≤q)

  mul-is-zero-ℚ-closed-interval-ℚ :
    ([p,q] : closed-interval-ℚ) (r : ℚ) (is-zero-r : is-zero-ℚ r) →
    mul-ℚ-closed-interval-ℚ [p,q] r ＝
    zero-zero-closed-interval-ℚ
  mul-is-zero-ℚ-closed-interval-ℚ ((p , q) , p≤q) _ refl =
    eq-closed-interval-ℚ _ _
      ( ( ap-min-ℚ
          ( right-zero-law-mul-ℚ _)
          ( right-zero-law-mul-ℚ _)) ∙
        ( idempotent-min-ℚ zero-ℚ))
      ( ( ap-max-ℚ
          ( right-zero-law-mul-ℚ _)
          ( right-zero-law-mul-ℚ _)) ∙
        ( idempotent-max-ℚ zero-ℚ))

  mul-is-in-closed-interval-ℚ-ℚ :
    ([p,q] : closed-interval-ℚ) (r s : ℚ) →
    is-in-closed-interval-ℚ [p,q] s →
    is-in-closed-interval-ℚ
      ( mul-ℚ-closed-interval-ℚ [p,q] r)
      ( s *ℚ r)
  mul-is-in-closed-interval-ℚ-ℚ [p,q] r s s∈[p,q] =
    trichotomy-sign-ℚ r
      ( λ neg-r →
        inv-tr
          ( λ [x,y] → is-in-closed-interval-ℚ [x,y] (s *ℚ r))
          ( mul-is-negative-ℚ-closed-interval-ℚ [p,q] r neg-r)
          ( mul-is-in-closed-interval-ℚ-ℚ⁻
            ( [p,q])
            ( r , neg-r)
            ( s)
            ( s∈[p,q])))
      ( λ r=0 →
        binary-tr
          ( is-in-closed-interval-ℚ)
          ( inv (mul-is-zero-ℚ-closed-interval-ℚ [p,q] r r=0))
          ( inv (ap-mul-ℚ refl r=0 ∙ right-zero-law-mul-ℚ s))
          ( refl-leq-ℚ zero-ℚ , refl-leq-ℚ zero-ℚ))
      ( λ pos-r →
        inv-tr
          ( λ [x,y] → is-in-closed-interval-ℚ [x,y] (s *ℚ r))
          ( mul-is-positive-ℚ-closed-interval-ℚ [p,q] r pos-r)
          ( mul-is-in-closed-interval-ℚ-ℚ⁺
            ( [p,q])
            ( r , pos-r)
            ( s)
            ( s∈[p,q])))

  is-in-im-mul-is-in-closed-interval-ℚ-ℚ :
    ([p,q] : closed-interval-ℚ) (r s : ℚ) →
    is-in-closed-interval-ℚ
      ( mul-ℚ-closed-interval-ℚ [p,q] r)
      ( s) →
    is-in-im-subtype (mul-ℚ' r) (subtype-closed-interval-ℚ [p,q]) s
  is-in-im-mul-is-in-closed-interval-ℚ-ℚ
    [p,q] r s s∈[min-pr-qr,max-pr-qr] =
    trichotomy-sign-ℚ r
      ( λ neg-r →
        is-in-im-is-in-mul-closed-interval-ℚ-ℚ⁻
          ( [p,q])
          ( r , neg-r)
          ( s)
          ( tr
            ( λ [x,y] → is-in-closed-interval-ℚ [x,y] s)
            ( mul-is-negative-ℚ-closed-interval-ℚ [p,q] r neg-r)
            ( s∈[min-pr-qr,max-pr-qr])))
      ( λ r=0 →
        inv-tr
          ( λ t →
            is-in-im-subtype
              ( mul-ℚ' t)
              ( subtype-closed-interval-ℚ [p,q])
              ( s))
          ( r=0)
          ( is-in-im-mul-is-in-zero-zero-closed-interval-ℚ
            ( [p,q])
            ( s)
            ( tr
              ( λ [x,y] → is-in-closed-interval-ℚ [x,y] s)
              ( mul-is-zero-ℚ-closed-interval-ℚ [p,q] r r=0)
              ( s∈[min-pr-qr,max-pr-qr]))))
      ( λ pos-r →
        is-in-im-is-in-mul-ℚ⁺-closed-interval-ℚ
          ( [p,q])
          ( r , pos-r)
          ( s)
          ( tr
            ( λ [x,y] → is-in-closed-interval-ℚ [x,y] s)
            ( mul-is-positive-ℚ-closed-interval-ℚ [p,q] r pos-r)
            ( s∈[min-pr-qr,max-pr-qr])))

  is-closed-interval-map-mul-ℚ-closed-interval-ℚ :
    (q : ℚ) ([a,b] : closed-interval-ℚ) →
    is-closed-interval-map-ℚ
      ( mul-ℚ' q)
      ( [a,b])
      ( mul-ℚ-closed-interval-ℚ [a,b] q)
  is-closed-interval-map-mul-ℚ-closed-interval-ℚ q [a,b] =
    ( ind-Σ (mul-is-in-closed-interval-ℚ-ℚ [a,b] q) ,
      ind-Σ (is-in-im-mul-is-in-closed-interval-ℚ-ℚ [a,b] q))
```

### Multiplication of a rational number and an interval

```agda
abstract
  commute-mul-ℚ-closed-interval-ℚ :
    ([p,q] : closed-interval-ℚ) (r : ℚ) →
    mul-ℚ-closed-interval-ℚ [p,q] r ＝
    mul-closed-interval-ℚ-ℚ r [p,q]
  commute-mul-ℚ-closed-interval-ℚ [p,q] r =
    eq-closed-interval-ℚ _ _
      ( ap-min-ℚ (commutative-mul-ℚ _ _) (commutative-mul-ℚ _ _))
      ( ap-max-ℚ (commutative-mul-ℚ _ _) (commutative-mul-ℚ _ _))

  mul-ℚ-is-in-closed-interval-ℚ :
    ([p,q] : closed-interval-ℚ) (r s : ℚ) →
    is-in-closed-interval-ℚ [p,q] s →
    is-in-closed-interval-ℚ
      ( mul-closed-interval-ℚ-ℚ r [p,q])
      ( r *ℚ s)
  mul-ℚ-is-in-closed-interval-ℚ [p,q] r s s∈[p,q] =
    binary-tr
      ( is-in-closed-interval-ℚ)
      ( commute-mul-ℚ-closed-interval-ℚ [p,q] r)
      ( commutative-mul-ℚ s r)
      ( mul-is-in-closed-interval-ℚ-ℚ [p,q] r s s∈[p,q])

  is-in-im-mul-ℚ-is-in-closed-interval-ℚ :
    ([p,q] : closed-interval-ℚ) (r s : ℚ) →
    is-in-closed-interval-ℚ
      ( mul-closed-interval-ℚ-ℚ r [p,q])
      ( s) →
    is-in-im-subtype (mul-ℚ r) (subtype-closed-interval-ℚ [p,q]) s
  is-in-im-mul-ℚ-is-in-closed-interval-ℚ
    [p,q] r s s∈[min-rp-rq,max-rp-rq] =
    tr
      ( λ f → is-in-im-subtype f (subtype-closed-interval-ℚ [p,q]) s)
      ( eq-htpy (λ _ → commutative-mul-ℚ _ _))
      ( is-in-im-mul-is-in-closed-interval-ℚ-ℚ [p,q] r s
        ( inv-tr
          ( λ [x,y] → is-in-closed-interval-ℚ [x,y] s)
          ( commute-mul-ℚ-closed-interval-ℚ [p,q] r)
          ( s∈[min-rp-rq,max-rp-rq])))

  is-closed-interval-map-mul-closed-interval-ℚ-ℚ :
    (q : ℚ) ([a,b] : closed-interval-ℚ) →
    is-closed-interval-map-ℚ
      ( mul-ℚ q)
      ( [a,b])
      ( mul-closed-interval-ℚ-ℚ q [a,b])
  is-closed-interval-map-mul-closed-interval-ℚ-ℚ q [a,b] =
    binary-tr
      ( λ f i → is-closed-interval-map-ℚ f [a,b] i)
      ( eq-htpy (λ _ → commutative-mul-ℚ _ _))
      ( commute-mul-ℚ-closed-interval-ℚ [a,b] q)
      ( is-closed-interval-map-mul-ℚ-closed-interval-ℚ q [a,b])
```

### Multiplication of two closed intervals

```agda
abstract
  is-in-mul-interval-mul-is-in-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) (p q : ℚ) →
    is-in-closed-interval-ℚ [a,b] p →
    is-in-closed-interval-ℚ [c,d] q →
    is-in-closed-interval-ℚ
      ( mul-closed-interval-ℚ [a,b] [c,d])
      ( p *ℚ q)
  is-in-mul-interval-mul-is-in-closed-interval-ℚ
    [a,b]@((a , b) , a≤b) [c,d]@((c , d) , c≤d) p q
    p∈[a,b]@(a≤p , p≤b) q∈[c,d]@(c≤q , q≤d) =
      let
        (min-aq-bq≤pq , pq≤max-aq-bq) =
          mul-is-in-closed-interval-ℚ-ℚ [a,b] q p p∈[a,b]
        (min-ac-ad≤aq , aq≤max-ac-ad) =
          mul-ℚ-is-in-closed-interval-ℚ [c,d] a q q∈[c,d]
        (min-bc-bd≤bq , bq≤max-bc-bd) =
          mul-ℚ-is-in-closed-interval-ℚ [c,d] b q q∈[c,d]
      in
        ( transitive-leq-ℚ
            ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d])
            ( _)
            ( p *ℚ q)
            ( min-aq-bq≤pq)
            ( min-leq-leq-ℚ _ _ _ _ min-ac-ad≤aq min-bc-bd≤bq) ,
          transitive-leq-ℚ
            ( p *ℚ q)
            ( _)
            ( upper-bound-mul-closed-interval-ℚ [a,b] [c,d])
            ( max-leq-leq-ℚ _ _ _ _ aq≤max-ac-ad bq≤max-bc-bd)
            ( pq≤max-aq-bq))

  is-in-minkowski-product-is-in-mul-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) → (q : ℚ) →
    is-in-closed-interval-ℚ
      ( mul-closed-interval-ℚ [a,b] [c,d])
      ( q) →
    is-in-subtype
      ( minkowski-mul-Commutative-Monoid
        ( commutative-monoid-mul-ℚ)
        ( subtype-closed-interval-ℚ [a,b])
        ( subtype-closed-interval-ℚ [c,d]))
      ( q)
  is-in-minkowski-product-is-in-mul-closed-interval-ℚ
    [a,b]@((a , b) , a≤b) [c,d]@((c , d) , c≤d) x x∈range =
    let
      motive =
        minkowski-mul-Commutative-Monoid
          ( commutative-monoid-mul-ℚ)
          ( subtype-closed-interval-ℚ [a,b])
          ( subtype-closed-interval-ℚ [c,d])
          ( x)
      open do-syntax-trunc-Prop motive
      case-[ac,ad] x∈[ac,ad] =
        do
          ((q , c≤q , q≤d) , aq=x) ←
            is-in-im-mul-ℚ-is-in-closed-interval-ℚ [c,d] a x x∈[ac,ad]
          intro-exists
            ( a , q)
            ( (refl-leq-ℚ a , a≤b) , (c≤q , q≤d) , inv aq=x)
      case-[ac,bc] x∈[ac,bc] =
        do
          ((p , a≤p , p≤b) , pc=x) ←
            is-in-im-mul-is-in-closed-interval-ℚ-ℚ [a,b] c x x∈[ac,bc]
          intro-exists
            ( p , c)
            ( (a≤p , p≤b) , (refl-leq-ℚ c , c≤d) , inv pc=x)
      case-[bc,bd] x∈[bc,bd] =
        do
          ((q , c≤q , q≤d) , bq=x) ←
            is-in-im-mul-ℚ-is-in-closed-interval-ℚ [c,d] b x x∈[bc,bd]
          intro-exists
            ( b , q)
            ( (a≤b , refl-leq-ℚ b) , (c≤q , q≤d) , inv bq=x)
      case-[ad,bd] x∈[ad,bd] =
        do
          ((p , a≤p , p≤b) , pd=x) ←
            is-in-im-mul-is-in-closed-interval-ℚ-ℚ [a,b] d x x∈[ad,bd]
          intro-exists
            ( p , d)
            ( (a≤p , p≤b) , (c≤d , refl-leq-ℚ d) , inv pd=x)
    in
      elim-disjunction motive
        ( elim-disjunction motive case-[ac,ad] case-[ac,bc])
        ( elim-disjunction motive case-[ad,bd] case-[bc,bd])
        ( cover-minimal-closed-interval-cover-of-four-elements-Total-Order
          ( ℚ-Total-Order)
          ( a *ℚ c)
          ( a *ℚ d)
          ( b *ℚ c)
          ( b *ℚ d)
          ( x)
          ( x∈range))
```

### Agreement with the Minkowski product

```agda
abstract
  has-same-elements-minkowski-mul-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    has-same-elements-subtype
      ( minkowski-mul-Commutative-Monoid
        ( commutative-monoid-mul-ℚ)
        ( subtype-closed-interval-ℚ [a,b])
        ( subtype-closed-interval-ℚ [c,d]))
      ( subtype-closed-interval-ℚ
        ( mul-closed-interval-ℚ [a,b] [c,d]))
  has-same-elements-minkowski-mul-closed-interval-ℚ [a,b] [c,d] x =
    ( rec-trunc-Prop
        ( subtype-closed-interval-ℚ
          ( mul-closed-interval-ℚ [a,b] [c,d])
          ( x))
        ( λ ((p , q) , p∈[a,b] , q∈[c,d] , x=pq) →
          inv-tr
            ( is-in-closed-interval-ℚ
              ( mul-closed-interval-ℚ [a,b] [c,d]))
            ( x=pq)
            ( is-in-mul-interval-mul-is-in-closed-interval-ℚ
              ( [a,b])
              ( [c,d])
              ( p)
              ( q)
              ( p∈[a,b])
              ( q∈[c,d]))) ,
      is-in-minkowski-product-is-in-mul-closed-interval-ℚ
        ( [a,b])
        ( [c,d])
        ( x))

  eq-minkowski-mul-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    minkowski-mul-Commutative-Monoid
      ( commutative-monoid-mul-ℚ)
      ( subtype-closed-interval-ℚ [a,b])
      ( subtype-closed-interval-ℚ [c,d]) ＝
    subtype-closed-interval-ℚ
      ( mul-closed-interval-ℚ [a,b] [c,d])
  eq-minkowski-mul-closed-interval-ℚ [a,b] [c,d] =
    eq-has-same-elements-subtype _ _
      ( has-same-elements-minkowski-mul-closed-interval-ℚ [a,b] [c,d])
```

### Associativity of multiplication of intervals

```agda
module _
  ([a,b] [c,d] [e,f] : closed-interval-ℚ)
  where

  abstract
    associative-mul-closed-interval-ℚ :
      mul-closed-interval-ℚ
        ( mul-closed-interval-ℚ [a,b] [c,d])
        ( [e,f]) ＝
      mul-closed-interval-ℚ
        ( [a,b])
        ( mul-closed-interval-ℚ [c,d] [e,f])
    associative-mul-closed-interval-ℚ =
      is-injective-subtype-closed-interval-ℚ
        ( equational-reasoning
          subtype-closed-interval-ℚ
            ( mul-closed-interval-ℚ
              ( mul-closed-interval-ℚ [a,b] [c,d])
              ( [e,f]))
          ＝
            minkowski-mul-Commutative-Monoid
              ( commutative-monoid-mul-ℚ)
              ( subtype-closed-interval-ℚ
                ( mul-closed-interval-ℚ [a,b] [c,d]))
              ( subtype-closed-interval-ℚ [e,f])
            by
              inv
                ( eq-minkowski-mul-closed-interval-ℚ
                  ( mul-closed-interval-ℚ [a,b] [c,d])
                  ( [e,f]))
          ＝
            minkowski-mul-Commutative-Monoid
              ( commutative-monoid-mul-ℚ)
              ( minkowski-mul-Commutative-Monoid
                ( commutative-monoid-mul-ℚ)
                ( subtype-closed-interval-ℚ [a,b])
                ( subtype-closed-interval-ℚ [c,d]))
              ( subtype-closed-interval-ℚ [e,f])
            by
              ap
                ( λ S →
                  minkowski-mul-Commutative-Monoid
                    ( commutative-monoid-mul-ℚ)
                    ( S)
                    ( subtype-closed-interval-ℚ [e,f]))
                ( inv
                  ( eq-minkowski-mul-closed-interval-ℚ [a,b] [c,d]))
          ＝
            minkowski-mul-Commutative-Monoid
              ( commutative-monoid-mul-ℚ)
              ( subtype-closed-interval-ℚ [a,b])
              ( minkowski-mul-Commutative-Monoid
                ( commutative-monoid-mul-ℚ)
                ( subtype-closed-interval-ℚ [c,d])
                ( subtype-closed-interval-ℚ [e,f]))
            by
              associative-minkowski-mul-Commutative-Monoid
                ( commutative-monoid-mul-ℚ)
                ( subtype-closed-interval-ℚ [a,b])
                ( subtype-closed-interval-ℚ [c,d])
                ( subtype-closed-interval-ℚ [e,f])
          ＝
            minkowski-mul-Commutative-Monoid
              ( commutative-monoid-mul-ℚ)
              ( subtype-closed-interval-ℚ [a,b])
              ( subtype-closed-interval-ℚ
                ( mul-closed-interval-ℚ [c,d] [e,f]))
            by
              ap
                ( minkowski-mul-Commutative-Monoid
                  ( commutative-monoid-mul-ℚ)
                  ( subtype-closed-interval-ℚ [a,b]))
                ( eq-minkowski-mul-closed-interval-ℚ [c,d] [e,f])
          ＝
            subtype-closed-interval-ℚ
              ( mul-closed-interval-ℚ
                ( [a,b])
                ( mul-closed-interval-ℚ [c,d] [e,f]))
              by
                eq-minkowski-mul-closed-interval-ℚ
                  ( [a,b])
                  ( mul-closed-interval-ℚ [c,d] [e,f]))
```

### Commutativity of multiplication of intervals

```agda
abstract
  commutative-mul-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    mul-closed-interval-ℚ [a,b] [c,d] ＝
    mul-closed-interval-ℚ [c,d] [a,b]
  commutative-mul-closed-interval-ℚ ((a , b) , a≤b) ((c , d) , c≤d) =
    eq-closed-interval-ℚ _ _
      ( ( interchange-law-min-Total-Order ℚ-Total-Order _ _ _ _) ∙
        ( ap-min-ℚ
          ( ap-min-ℚ (commutative-mul-ℚ _ _) (commutative-mul-ℚ _ _))
          ( ap-min-ℚ (commutative-mul-ℚ _ _) (commutative-mul-ℚ _ _))))
      ( ( interchange-law-max-Total-Order ℚ-Total-Order _ _ _ _) ∙
        ( ap-max-ℚ
          ( ap-max-ℚ (commutative-mul-ℚ _ _) (commutative-mul-ℚ _ _))
          ( ap-max-ℚ (commutative-mul-ℚ _ _) (commutative-mul-ℚ _ _))))
```

### Unit laws of multiplication of intervals

```agda
abstract
  left-unit-law-mul-closed-interval-ℚ :
    ([a,b] : closed-interval-ℚ) →
    mul-closed-interval-ℚ one-one-closed-interval-ℚ [a,b] ＝
    [a,b]
  left-unit-law-mul-closed-interval-ℚ ((a , b) , a≤b) =
    eq-closed-interval-ℚ _ _
      ( ( idempotent-min-ℚ _) ∙
        ( ap-min-ℚ (left-unit-law-mul-ℚ a) (left-unit-law-mul-ℚ b)) ∙
        ( left-leq-right-min-ℚ _ _ a≤b))
      ( ( idempotent-max-ℚ _) ∙
        ( ap-max-ℚ (left-unit-law-mul-ℚ a) (left-unit-law-mul-ℚ b)) ∙
        ( left-leq-right-max-ℚ _ _ a≤b))

  right-unit-law-mul-closed-interval-ℚ :
    ([a,b] : closed-interval-ℚ) →
    mul-closed-interval-ℚ [a,b] one-one-closed-interval-ℚ ＝
    [a,b]
  right-unit-law-mul-closed-interval-ℚ [a,b] =
    ( commutative-mul-closed-interval-ℚ
      ( [a,b])
      ( one-one-closed-interval-ℚ)) ∙
    ( left-unit-law-mul-closed-interval-ℚ [a,b])
```

### The commutative monoid of multiplication of rational intervals

```agda
semigroup-mul-closed-interval-ℚ : Semigroup lzero
semigroup-mul-closed-interval-ℚ =
  ( set-closed-interval-ℚ ,
    mul-closed-interval-ℚ ,
    associative-mul-closed-interval-ℚ)

monoid-mul-closed-interval-ℚ : Monoid lzero
monoid-mul-closed-interval-ℚ =
  ( semigroup-mul-closed-interval-ℚ ,
    one-one-closed-interval-ℚ ,
    left-unit-law-mul-closed-interval-ℚ ,
    right-unit-law-mul-closed-interval-ℚ)

commutative-monoid-mul-closed-interval-ℚ : Commutative-Monoid lzero
commutative-monoid-mul-closed-interval-ℚ =
  ( monoid-mul-closed-interval-ℚ ,
    commutative-mul-closed-interval-ℚ)
```

### Negative laws for interval multiplication

```agda
abstract
  right-negative-law-lower-bound-mul-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    lower-bound-mul-closed-interval-ℚ [a,b] (neg-closed-interval-ℚ [c,d]) ＝
    neg-ℚ (upper-bound-mul-closed-interval-ℚ [a,b] [c,d])
  right-negative-law-lower-bound-mul-closed-interval-ℚ
    ((a , b) , a≤b) ((c , d) , c≤d) =
    equational-reasoning
      min-ℚ
        ( min-ℚ (a *ℚ neg-ℚ d) (a *ℚ neg-ℚ c))
        ( min-ℚ (b *ℚ neg-ℚ d) (b *ℚ neg-ℚ c))
      ＝
        min-ℚ
          ( min-ℚ (a *ℚ neg-ℚ c) (a *ℚ neg-ℚ d))
          ( min-ℚ (b *ℚ neg-ℚ c) (b *ℚ neg-ℚ d))
        by ap-min-ℚ (commutative-min-ℚ _ _) (commutative-min-ℚ _ _)
      ＝
        min-ℚ
          ( min-ℚ (neg-ℚ (a *ℚ c)) (neg-ℚ (a *ℚ d)))
          ( min-ℚ (neg-ℚ (b *ℚ c)) (neg-ℚ (b *ℚ d)))
        by
          ap-min-ℚ
            ( ap-min-ℚ
              ( right-negative-law-mul-ℚ _ _)
              ( right-negative-law-mul-ℚ _ _))
            ( ap-min-ℚ
              ( right-negative-law-mul-ℚ _ _)
              ( right-negative-law-mul-ℚ _ _))
      ＝
        min-ℚ
          ( neg-ℚ (max-ℚ (a *ℚ c) (a *ℚ d)))
          ( neg-ℚ (max-ℚ (b *ℚ c) (b *ℚ d)))
        by inv (ap-min-ℚ (neg-max-ℚ _ _) (neg-max-ℚ _ _))
      ＝
        neg-ℚ
          ( max-ℚ
            ( max-ℚ (a *ℚ c) (a *ℚ d))
            ( max-ℚ (b *ℚ c) (b *ℚ d)))
        by inv (neg-max-ℚ _ _)

  right-negative-law-upper-bound-mul-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    upper-bound-mul-closed-interval-ℚ [a,b] (neg-closed-interval-ℚ [c,d]) ＝
    neg-ℚ (lower-bound-mul-closed-interval-ℚ [a,b] [c,d])
  right-negative-law-upper-bound-mul-closed-interval-ℚ
    ((a , b) , a≤b) ((c , d) , c≤d) =
    equational-reasoning
      max-ℚ
        ( max-ℚ (a *ℚ neg-ℚ d) (a *ℚ neg-ℚ c))
        ( max-ℚ (b *ℚ neg-ℚ d) (b *ℚ neg-ℚ c))
      ＝
        max-ℚ
          ( max-ℚ (a *ℚ neg-ℚ c) (a *ℚ neg-ℚ d))
          ( max-ℚ (b *ℚ neg-ℚ c) (b *ℚ neg-ℚ d))
        by ap-max-ℚ (commutative-max-ℚ _ _) (commutative-max-ℚ _ _)
      ＝
        max-ℚ
          ( max-ℚ (neg-ℚ (a *ℚ c)) (neg-ℚ (a *ℚ d)))
          ( max-ℚ (neg-ℚ (b *ℚ c)) (neg-ℚ (b *ℚ d)))
        by
          ap-max-ℚ
            ( ap-max-ℚ
              ( right-negative-law-mul-ℚ _ _)
              ( right-negative-law-mul-ℚ _ _))
            ( ap-max-ℚ
              ( right-negative-law-mul-ℚ _ _)
              ( right-negative-law-mul-ℚ _ _))
      ＝
        max-ℚ
          ( neg-ℚ (min-ℚ (a *ℚ c) (a *ℚ d)))
          ( neg-ℚ (min-ℚ (b *ℚ c) (b *ℚ d)))
        by inv (ap-max-ℚ (neg-min-ℚ _ _) (neg-min-ℚ _ _))
      ＝ neg-ℚ (min-ℚ (min-ℚ (a *ℚ c) (a *ℚ d)) (min-ℚ (b *ℚ c) (b *ℚ d)))
        by inv (neg-min-ℚ _ _)

  right-negative-law-mul-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    mul-closed-interval-ℚ [a,b] (neg-closed-interval-ℚ [c,d]) ＝
    neg-closed-interval-ℚ (mul-closed-interval-ℚ [a,b] [c,d])
  right-negative-law-mul-closed-interval-ℚ [a,b] [c,d] =
    eq-closed-interval-ℚ _ _
      ( right-negative-law-lower-bound-mul-closed-interval-ℚ [a,b] [c,d])
      ( right-negative-law-upper-bound-mul-closed-interval-ℚ [a,b] [c,d])

  left-negative-law-mul-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    mul-closed-interval-ℚ (neg-closed-interval-ℚ [a,b]) [c,d] ＝
    neg-closed-interval-ℚ (mul-closed-interval-ℚ [a,b] [c,d])
  left-negative-law-mul-closed-interval-ℚ [a,b] [c,d] =
    equational-reasoning
      mul-closed-interval-ℚ (neg-closed-interval-ℚ [a,b]) [c,d]
      ＝ mul-closed-interval-ℚ [c,d] (neg-closed-interval-ℚ [a,b])
        by commutative-mul-closed-interval-ℚ (neg-closed-interval-ℚ [a,b]) [c,d]
      ＝ neg-closed-interval-ℚ (mul-closed-interval-ℚ [c,d] [a,b])
        by right-negative-law-mul-closed-interval-ℚ [c,d] [a,b]
      ＝ neg-closed-interval-ℚ (mul-closed-interval-ℚ [a,b] [c,d])
        by
          ap
            ( neg-closed-interval-ℚ)
            ( commutative-mul-closed-interval-ℚ [c,d] [a,b])
```

### The sign of interval boundaries

```agda
abstract
  is-nonnegative-left-lower-bound-eq-lower-bound-mul-interval-mul-lower-bound-nontrivial-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    (a<b : is-proper-closed-interval-ℚ [a,b]) →
    (c<d : is-proper-closed-interval-ℚ [c,d]) →
    ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d] ＝
      ( lower-bound-closed-interval-ℚ [a,b] *ℚ
        lower-bound-closed-interval-ℚ [c,d])) →
    is-nonnegative-ℚ (lower-bound-closed-interval-ℚ [a,b])
  is-nonnegative-left-lower-bound-eq-lower-bound-mul-interval-mul-lower-bound-nontrivial-closed-interval-ℚ
    ((a , b) , _) ((c , d) , _) a<b c<d min=ac =
    rec-coproduct
      ( λ is-neg-a →
        ex-falso
          ( not-leq-le-ℚ
            ( a *ℚ d)
            ( a *ℚ c)
            ( reverses-le-left-mul-ℚ⁻ (a , is-neg-a) c d c<d)
            ( tr
              ( λ q → leq-ℚ q (a *ℚ d))
              ( min=ac)
              ( transitive-leq-ℚ _ _ _
                ( leq-right-min-ℚ _ _)
                ( leq-left-min-ℚ _ _)))))
      ( id)
      ( decide-is-negative-is-nonnegative-ℚ a)

  is-nonnegative-right-lower-bound-eq-lower-bound-mul-interval-mul-lower-bound-nontrivial-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    (a<b : is-proper-closed-interval-ℚ [a,b]) →
    (c<d : is-proper-closed-interval-ℚ [c,d]) →
    ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d] ＝
      ( lower-bound-closed-interval-ℚ [a,b] *ℚ
        lower-bound-closed-interval-ℚ [c,d])) →
    is-nonnegative-ℚ (lower-bound-closed-interval-ℚ [c,d])
  is-nonnegative-right-lower-bound-eq-lower-bound-mul-interval-mul-lower-bound-nontrivial-closed-interval-ℚ
    ((a , b) , _) ((c , d) , _) a<b c<d min=ac =
    rec-coproduct
      ( λ is-neg-c →
        ex-falso
          ( not-leq-le-ℚ
            ( b *ℚ c)
            ( a *ℚ c)
            ( reverses-le-right-mul-ℚ⁻ (c , is-neg-c) a b a<b)
            ( tr
              ( λ q → leq-ℚ q (b *ℚ c))
              ( min=ac)
              ( transitive-leq-ℚ _ _ _
                ( leq-left-min-ℚ _ _)
                ( leq-right-min-ℚ _ _)))))
      ( id)
      ( decide-is-negative-is-nonnegative-ℚ c)

  is-nonpositive-left-lower-bound-eq-lower-bound-mul-interval-mul-lower-upper-bound-nontrivial-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    (a<b : is-proper-closed-interval-ℚ [a,b]) →
    (c<d : is-proper-closed-interval-ℚ [c,d]) →
    ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d] ＝
      ( lower-bound-closed-interval-ℚ [a,b] *ℚ
        upper-bound-closed-interval-ℚ [c,d])) →
    is-nonpositive-ℚ (lower-bound-closed-interval-ℚ [a,b])
  is-nonpositive-left-lower-bound-eq-lower-bound-mul-interval-mul-lower-upper-bound-nontrivial-closed-interval-ℚ
    ((a , b) , _) ((c , d) , _) a<b c<d min=ad =
    rec-coproduct
      ( λ is-pos-a →
        ex-falso
          ( not-leq-le-ℚ
            ( a *ℚ c)
            ( a *ℚ d)
            ( preserves-le-left-mul-ℚ⁺ (a , is-pos-a) c d c<d)
            ( tr
              ( λ q → leq-ℚ q (a *ℚ c))
              ( min=ad)
              ( transitive-leq-ℚ _ _ _
                ( leq-left-min-ℚ _ _)
                ( leq-left-min-ℚ _ _)))))
      ( id)
      ( decide-is-positive-is-nonpositive-ℚ a)

  is-nonnegative-right-upper-bound-eq-lower-bound-mul-interval-mul-lower-upper-bound-nontrivial-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    (a<b : is-proper-closed-interval-ℚ [a,b]) →
    (c<d : is-proper-closed-interval-ℚ [c,d]) →
    ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d] ＝
      ( lower-bound-closed-interval-ℚ [a,b] *ℚ
        upper-bound-closed-interval-ℚ [c,d])) →
    is-nonnegative-ℚ (upper-bound-closed-interval-ℚ [c,d])
  is-nonnegative-right-upper-bound-eq-lower-bound-mul-interval-mul-lower-upper-bound-nontrivial-closed-interval-ℚ
    ((a , b) , _) ((c , d) , _) a<b c<d min=ad =
    rec-coproduct
      ( λ is-neg-d →
        ex-falso
          ( not-leq-le-ℚ
            ( b *ℚ d)
            ( a *ℚ d)
            ( reverses-le-right-mul-ℚ⁻ (d , is-neg-d) a b a<b)
            ( tr
              ( λ q → leq-ℚ q (b *ℚ d))
              ( min=ad)
              ( transitive-leq-ℚ _ _ _
                ( leq-right-min-ℚ _ _)
                ( leq-right-min-ℚ _ _)))))
      ( id)
      ( decide-is-negative-is-nonnegative-ℚ d)

  is-nonnegative-left-upper-bound-eq-lower-bound-mul-interval-mul-upper-lower-bound-nontrivial-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    (a<b : is-proper-closed-interval-ℚ [a,b]) →
    (c<d : is-proper-closed-interval-ℚ [c,d]) →
    ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d] ＝
      ( upper-bound-closed-interval-ℚ [a,b] *ℚ
        lower-bound-closed-interval-ℚ [c,d])) →
    is-nonnegative-ℚ (upper-bound-closed-interval-ℚ [a,b])
  is-nonnegative-left-upper-bound-eq-lower-bound-mul-interval-mul-upper-lower-bound-nontrivial-closed-interval-ℚ
    ((a , b) , _) ((c , d) , _) a<b c<d min=bc =
    rec-coproduct
      ( λ is-neg-b →
        ex-falso
          ( not-leq-le-ℚ
            ( b *ℚ d)
            ( b *ℚ c)
            ( reverses-le-left-mul-ℚ⁻ (b , is-neg-b) c d c<d)
            ( tr
              ( λ q → leq-ℚ q (b *ℚ d))
              ( min=bc)
              ( transitive-leq-ℚ _ _ _
                ( leq-right-min-ℚ _ _)
                ( leq-right-min-ℚ _ _)))))
      ( id)
      ( decide-is-negative-is-nonnegative-ℚ b)

  is-nonpositive-right-lower-bound-eq-lower-bound-mul-interval-mul-upper-lower-bound-nontrivial-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    (a<b : is-proper-closed-interval-ℚ [a,b]) →
    (c<d : is-proper-closed-interval-ℚ [c,d]) →
    ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d] ＝
      ( upper-bound-closed-interval-ℚ [a,b] *ℚ
        lower-bound-closed-interval-ℚ [c,d])) →
    is-nonpositive-ℚ (lower-bound-closed-interval-ℚ [c,d])
  is-nonpositive-right-lower-bound-eq-lower-bound-mul-interval-mul-upper-lower-bound-nontrivial-closed-interval-ℚ
    ((a , b) , _) ((c , d) , _) a<b c<d min=bc =
    rec-coproduct
      ( λ is-pos-c →
        ex-falso
          ( not-leq-le-ℚ
            ( a *ℚ c)
            ( b *ℚ c)
            ( preserves-le-right-mul-ℚ⁺ (c , is-pos-c) a b a<b)
            ( tr
              ( λ q → leq-ℚ q (a *ℚ c))
              ( min=bc)
              ( transitive-leq-ℚ _ _ _
                ( leq-left-min-ℚ _ _)
                ( leq-left-min-ℚ _ _)))))
      ( id)
      ( decide-is-positive-is-nonpositive-ℚ c)

  is-nonpositive-left-upper-bound-eq-lower-bound-mul-interval-mul-upper-bound-nontrivial-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    (a<b : is-proper-closed-interval-ℚ [a,b]) →
    (c<d : is-proper-closed-interval-ℚ [c,d]) →
    ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d] ＝
      ( upper-bound-closed-interval-ℚ [a,b] *ℚ
        upper-bound-closed-interval-ℚ [c,d])) →
    is-nonpositive-ℚ (upper-bound-closed-interval-ℚ [a,b])
  is-nonpositive-left-upper-bound-eq-lower-bound-mul-interval-mul-upper-bound-nontrivial-closed-interval-ℚ
    ((a , b) , _) ((c , d) , _) a<b c<d min=bd =
    rec-coproduct
      ( λ is-pos-b →
        ex-falso
          ( not-leq-le-ℚ
            ( b *ℚ c)
            ( b *ℚ d)
            ( preserves-le-left-mul-ℚ⁺ (b , is-pos-b) c d c<d)
            ( tr
              ( λ q → leq-ℚ q (b *ℚ c))
              ( min=bd)
              ( transitive-leq-ℚ _ _ _
                ( leq-left-min-ℚ _ _)
                ( leq-right-min-ℚ _ _)))))
      ( id)
      ( decide-is-positive-is-nonpositive-ℚ b)

  is-nonpositive-right-upper-bound-eq-lower-bound-mul-interval-mul-upper-bound-nontrivial-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    (a<b : is-proper-closed-interval-ℚ [a,b]) →
    (c<d : is-proper-closed-interval-ℚ [c,d]) →
    ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d] ＝
      ( upper-bound-closed-interval-ℚ [a,b] *ℚ
        upper-bound-closed-interval-ℚ [c,d])) →
    is-nonpositive-ℚ (upper-bound-closed-interval-ℚ [c,d])
  is-nonpositive-right-upper-bound-eq-lower-bound-mul-interval-mul-upper-bound-nontrivial-closed-interval-ℚ
    ((a , b) , _) ((c , d) , _) a<b c<d min=bd =
    rec-coproduct
      ( λ is-pos-d →
        ex-falso
          ( not-leq-le-ℚ
            ( a *ℚ d)
            ( b *ℚ d)
            ( preserves-le-right-mul-ℚ⁺ (d , is-pos-d) a b a<b)
            ( tr
              ( λ q → leq-ℚ q (a *ℚ d))
              ( min=bd)
              ( transitive-leq-ℚ _ _ _
                ( leq-right-min-ℚ _ _)
                ( leq-left-min-ℚ _ _)))))
      ( id)
      ( decide-is-positive-is-nonpositive-ℚ d)
```

### Multiplication of interior intervals

```agda
abstract
  le-lower-bound-mul-interior-closed-interval-ℚ :
    ([a,b] [c,d] [a',b'] [c',d'] : closed-interval-ℚ) →
    is-interior-closed-interval-ℚ [a,b] [a',b'] →
    is-interior-closed-interval-ℚ [c,d] [c',d'] →
    is-proper-closed-interval-ℚ [a',b'] →
    is-proper-closed-interval-ℚ [c',d'] →
    le-ℚ
      ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d])
      ( lower-bound-mul-closed-interval-ℚ [a',b'] [c',d'])
  le-lower-bound-mul-interior-closed-interval-ℚ
    [a,b]@((a , b) , _) [c,d]@((c , d) , _)
    [a',b']@((a' , b') , _) [c',d']@((c' , d') , _)
    (a<a' , b'<b) (c<c' , d'<d) a'<b' c'<d' =
    let
      min' = lower-bound-mul-closed-interval-ℚ [a',b'] [c',d']
      min = lower-bound-mul-closed-interval-ℚ [a,b] [c,d]
      min≤ac : leq-ℚ min (a *ℚ c)
      min≤ac = transitive-leq-ℚ _ _ _ (leq-left-min-ℚ _ _) (leq-left-min-ℚ _ _)
      min≤ad : leq-ℚ min (a *ℚ d)
      min≤ad = transitive-leq-ℚ _ _ _ (leq-right-min-ℚ _ _) (leq-left-min-ℚ _ _)
      min≤bc : leq-ℚ min (b *ℚ c)
      min≤bc = transitive-leq-ℚ _ _ _ (leq-left-min-ℚ _ _) (leq-right-min-ℚ _ _)
      min≤bd : leq-ℚ min (b *ℚ d)
      min≤bd =
        transitive-leq-ℚ _ _ _ (leq-right-min-ℚ _ _) (leq-right-min-ℚ _ _)
    in
      eq-one-of-four-min-Total-Order
        ( ℚ-Total-Order)
        ( le-ℚ-Prop min min')
        ( a' *ℚ c')
        ( a' *ℚ d')
        ( b' *ℚ c')
        ( b' *ℚ d')
        ( λ min'=a'c' →
          let
            is-nonneg-a' =
              is-nonnegative-left-lower-bound-eq-lower-bound-mul-interval-mul-lower-bound-nontrivial-closed-interval-ℚ
                ( [a',b'])
                ( [c',d'])
                ( a'<b')
                ( c'<d')
                ( min'=a'c')
            is-nonneg-c' =
              is-nonnegative-right-lower-bound-eq-lower-bound-mul-interval-mul-lower-bound-nontrivial-closed-interval-ℚ
                ( [a',b'])
                ( [c',d'])
                ( a'<b')
                ( c'<d')
                ( min'=a'c')
            is-pos-b' =
              is-positive-le-nonnegative-ℚ (a' , is-nonneg-a') b' a'<b'
            is-pos-b = is-positive-le-ℚ⁺ (b' , is-pos-b') b b'<b
            is-pos-d' =
              is-positive-le-nonnegative-ℚ (c' , is-nonneg-c') d' c'<d'
            is-pos-d = is-positive-le-ℚ⁺ (d' , is-pos-d') d d'<d
            is-nonneg-min' =
              inv-tr
                ( is-nonnegative-ℚ)
                ( min'=a'c')
                ( is-nonnegative-mul-ℚ a' c' is-nonneg-a' is-nonneg-c')
          in
            rec-coproduct
              ( λ is-neg-a →
                concatenate-leq-le-ℚ
                  ( min)
                  ( a *ℚ d)
                  ( min')
                  ( min≤ad)
                  ( le-negative-nonnegative-ℚ
                    ( mul-negative-positive-ℚ (a , is-neg-a) (d , is-pos-d))
                    ( min' , is-nonneg-min')))
              ( λ is-nonneg-a →
                rec-coproduct
                  ( λ is-neg-c →
                    concatenate-leq-le-ℚ
                      ( lower-bound-mul-closed-interval-ℚ [a,b] [c,d])
                      ( b *ℚ c)
                      ( lower-bound-mul-closed-interval-ℚ [a',b'] [c',d'])
                      ( min≤bc)
                      ( le-negative-nonnegative-ℚ
                        ( mul-positive-negative-ℚ (b , is-pos-b) (c , is-neg-c))
                        ( min' , is-nonneg-min')))
                  ( λ is-nonneg-c →
                    concatenate-leq-le-ℚ
                      ( min)
                      ( a *ℚ c')
                      ( min')
                      ( transitive-leq-ℚ
                        ( min)
                        ( a *ℚ c)
                        ( a *ℚ c')
                        ( preserves-leq-left-mul-ℚ⁰⁺
                          ( a , is-nonneg-a)
                          ( c)
                          ( c')
                          ( leq-le-ℚ c<c'))
                        ( min≤ac))
                      ( inv-tr
                        ( le-ℚ (a *ℚ c'))
                        ( min'=a'c')
                        ( preserves-le-right-mul-ℚ⁺
                          ( c' ,
                            is-positive-le-nonnegative-ℚ
                              ( c , is-nonneg-c)
                              ( c')
                              ( c<c'))
                          ( a)
                          ( a')
                          ( a<a'))))
                  ( decide-is-negative-is-nonnegative-ℚ c))
              ( decide-is-negative-is-nonnegative-ℚ a))
        ( λ min'=a'd' →
          let
            is-nonpos-a' =
              is-nonpositive-left-lower-bound-eq-lower-bound-mul-interval-mul-lower-upper-bound-nontrivial-closed-interval-ℚ
                ( [a',b'])
                ( [c',d'])
                ( a'<b')
                ( c'<d')
                ( min'=a'd')
            is-nonneg-d' =
              is-nonnegative-right-upper-bound-eq-lower-bound-mul-interval-mul-lower-upper-bound-nontrivial-closed-interval-ℚ
                ( [a',b'])
                ( [c',d'])
                ( a'<b')
                ( c'<d')
                ( min'=a'd')
            is-neg-a =
              is-negative-le-nonpositive-ℚ (a' , is-nonpos-a') a a<a'
            is-pos-d =
              is-positive-le-nonnegative-ℚ (d' , is-nonneg-d') d d'<d
          in
            concatenate-leq-le-ℚ
              ( min)
              ( a *ℚ d)
              ( min')
              ( transitive-leq-ℚ _ _ _
                ( leq-right-min-ℚ _ _)
                ( leq-left-min-ℚ _ _))
              ( concatenate-le-leq-ℚ
                ( a *ℚ d)
                ( a *ℚ d')
                ( min')
                ( reverses-le-left-mul-ℚ⁻ (a , is-neg-a) d' d d'<d)
                ( inv-tr
                  ( leq-ℚ (a *ℚ d'))
                  ( min'=a'd')
                  ( preserves-leq-right-mul-ℚ⁰⁺
                    ( d' , is-nonneg-d')
                    ( a)
                    ( a')
                    ( leq-le-ℚ a<a')))))
        ( λ min'=b'c' →
          let
            is-nonneg-b' =
              is-nonnegative-left-upper-bound-eq-lower-bound-mul-interval-mul-upper-lower-bound-nontrivial-closed-interval-ℚ
                ( [a',b'])
                ( [c',d'])
                ( a'<b')
                ( c'<d')
                ( min'=b'c')
            is-nonpos-c' =
              is-nonpositive-right-lower-bound-eq-lower-bound-mul-interval-mul-upper-lower-bound-nontrivial-closed-interval-ℚ
                ( [a',b'])
                ( [c',d'])
                ( a'<b')
                ( c'<d')
                ( min'=b'c')
            is-pos-b = is-positive-le-nonnegative-ℚ (b' , is-nonneg-b') b b'<b
            is-neg-c = is-negative-le-nonpositive-ℚ (c' , is-nonpos-c') c c<c'
          in
            concatenate-le-leq-ℚ
              ( min)
              ( b' *ℚ c)
              ( min')
              ( concatenate-leq-le-ℚ
                ( min)
                ( b *ℚ c)
                ( b' *ℚ c)
                ( min≤bc)
                ( reverses-le-right-mul-ℚ⁻ (c , is-neg-c) b' b b'<b))
              ( inv-tr
                ( leq-ℚ (b' *ℚ c))
                ( min'=b'c')
                ( preserves-leq-left-mul-ℚ⁰⁺
                  ( b' , is-nonneg-b')
                  ( c)
                  ( c')
                  ( leq-le-ℚ c<c'))))
        ( λ min'=b'd' →
          let
            is-nonpos-b' =
              is-nonpositive-left-upper-bound-eq-lower-bound-mul-interval-mul-upper-bound-nontrivial-closed-interval-ℚ
                ( [a',b'])
                ( [c',d'])
                ( a'<b')
                ( c'<d')
                ( min'=b'd')
            is-nonpos-d' =
              is-nonpositive-right-upper-bound-eq-lower-bound-mul-interval-mul-upper-bound-nontrivial-closed-interval-ℚ
                ( [a',b'])
                ( [c',d'])
                ( a'<b')
                ( c'<d')
                ( min'=b'd')
            is-neg-a' =
              is-negative-le-nonpositive-ℚ (b' , is-nonpos-b') a' a'<b'
            is-neg-a = is-negative-le-ℚ⁻ (a' , is-neg-a') a a<a'
            is-neg-c' =
              is-negative-le-nonpositive-ℚ (d' , is-nonpos-d') c' c'<d'
            is-neg-c = is-negative-le-ℚ⁻ (c' , is-neg-c') c c<c'
            is-nonneg-min' =
              inv-tr
                ( is-nonnegative-ℚ)
                ( min'=b'd')
                ( is-nonnegative-mul-nonpositive-ℚ is-nonpos-b' is-nonpos-d')
          in
            rec-coproduct
              ( λ is-pos-b →
                concatenate-leq-le-ℚ
                  ( min)
                  ( b *ℚ c)
                  ( min')
                  ( min≤bc)
                  ( le-negative-nonnegative-ℚ
                    ( mul-positive-negative-ℚ (b , is-pos-b) (c , is-neg-c))
                    ( min' , is-nonneg-min')))
              ( λ is-nonpos-b →
                rec-coproduct
                  ( λ is-pos-d →
                    concatenate-leq-le-ℚ
                      ( min)
                      ( a *ℚ d)
                      ( min')
                      ( min≤ad)
                      ( le-negative-nonnegative-ℚ
                        ( mul-negative-positive-ℚ (a , is-neg-a) (d , is-pos-d))
                        ( min' , is-nonneg-min')))
                  ( λ is-nonpos-d →
                    concatenate-leq-le-ℚ
                      ( min)
                      ( b *ℚ d)
                      ( min')
                      ( min≤bd)
                      ( concatenate-leq-le-ℚ
                        ( b *ℚ d)
                        ( b' *ℚ d)
                        ( min')
                        ( reverses-leq-right-mul-ℚ⁰⁻
                          ( d , is-nonpos-d)
                          ( b')
                          ( b)
                          ( leq-le-ℚ b'<b))
                        ( inv-tr
                          ( le-ℚ (b' *ℚ d))
                          ( min'=b'd')
                          ( reverses-le-left-mul-ℚ⁻
                            ( b' ,
                              is-negative-le-nonpositive-ℚ
                                ( b , is-nonpos-b)
                                ( b')
                                ( b'<b))
                            ( d')
                            ( d)
                            ( d'<d)))))
                  ( decide-is-positive-is-nonpositive-ℚ d))
              ( decide-is-positive-is-nonpositive-ℚ b))

  le-upper-bound-mul-interior-closed-interval-ℚ :
    ([a,b] [c,d] [a',b'] [c',d'] : closed-interval-ℚ) →
    is-interior-closed-interval-ℚ [a,b] [a',b'] →
    is-interior-closed-interval-ℚ [c,d] [c',d'] →
    is-proper-closed-interval-ℚ [a',b'] →
    is-proper-closed-interval-ℚ [c',d'] →
    le-ℚ
      ( upper-bound-mul-closed-interval-ℚ [a',b'] [c',d'])
      ( upper-bound-mul-closed-interval-ℚ [a,b] [c,d])
  le-upper-bound-mul-interior-closed-interval-ℚ
    [a,b]@((a , b) , _) [c,d]@((c , d) , _)
    [a',b']@((a' , b') , _) [c',d']@((c' , d') , _)
    (a<a' , b'<b) (c<c' , d'<d) a'<b' c'<d' =
    binary-tr
      ( le-ℚ)
      ( ( ap
          ( neg-ℚ)
          ( right-negative-law-lower-bound-mul-closed-interval-ℚ
            ( [a',b'])
            ( [c',d']))) ∙
        ( neg-neg-ℚ _))
      ( ( ap
          ( neg-ℚ)
          ( right-negative-law-lower-bound-mul-closed-interval-ℚ [a,b] [c,d])) ∙
        ( neg-neg-ℚ _))
      ( neg-le-ℚ _ _
        ( le-lower-bound-mul-interior-closed-interval-ℚ
          ( [a,b])
          ( neg-closed-interval-ℚ [c,d])
          ( [a',b'])
          ( neg-closed-interval-ℚ [c',d'])
          ( a<a' , b'<b)
          ( is-interior-neg-closed-interval-ℚ [c,d] [c',d'] (c<c' , d'<d))
          ( a'<b')
          ( is-nontrivial-neg-closed-interval-ℚ [c',d'] c'<d')))

  is-interior-mul-closed-interval-ℚ :
    ([a,b] [c,d] [a',b'] [c',d'] : closed-interval-ℚ) →
    is-interior-closed-interval-ℚ [a,b] [a',b'] →
    is-interior-closed-interval-ℚ [c,d] [c',d'] →
    is-proper-closed-interval-ℚ [a',b'] →
    is-proper-closed-interval-ℚ [c',d'] →
    is-interior-closed-interval-ℚ
      ( mul-closed-interval-ℚ [a,b] [c,d])
      ( mul-closed-interval-ℚ [a',b'] [c',d'])
  is-interior-mul-closed-interval-ℚ
    [a,b] [c,d] [a',b'] [c',d'] a<a'≤b'<b c<c'≤d'<d a'<b' c'<d' =
    ( le-lower-bound-mul-interior-closed-interval-ℚ
        ( [a,b])
        ( [c,d])
        ( [a',b'])
        ( [c',d'])
        ( a<a'≤b'<b)
        ( c<c'≤d'<d)
        ( a'<b')
        ( c'<d') ,
      le-upper-bound-mul-interior-closed-interval-ℚ
        ( [a,b])
        ( [c,d])
        ( [a',b'])
        ( [c',d'])
        ( a<a'≤b'<b)
        ( c<c'≤d'<d)
        ( a'<b')
        ( c'<d'))
```
