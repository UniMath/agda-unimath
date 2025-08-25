# Multiplication on intervals in the rational numbers

```agda
module elementary-number-theory.multiplication-intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.decidable-total-order-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.intervals-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.multiplicative-group-of-rational-numbers
open import elementary-number-theory.multiplicative-monoid-of-rational-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.function-extensionality
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
```

</details>

## Idea

Given two [intervals](elementary-number-theory.intervals-rational-numbers.md)
`[a, b]` and `[c, d]` in the
[rational numbers](elementary-number-theory.rational-numbers.md), the
[Minkowski product](group-theory.minkowski-multiplications-commutative-monoids.md)
of those intervals (interpreted as [subtypes](foundation.subtypes.md) of `ℚ`)
agrees with the interval `[min(ac, ad, bc, bd), max(ac, ad, bc, bd)]`.

## Definition

```agda
mul-right-interval-ℚ : ℚ → interval-ℚ → interval-ℚ
mul-right-interval-ℚ a ((b , c) , _) =
  unordered-interval-ℚ (a *ℚ b) (a *ℚ c)

mul-left-interval-ℚ : interval-ℚ → ℚ → interval-ℚ
mul-left-interval-ℚ ((a , b) , _) c =
  unordered-interval-ℚ (a *ℚ c) (b *ℚ c)

lower-bound-mul-interval-ℚ : interval-ℚ → interval-ℚ → ℚ
lower-bound-mul-interval-ℚ ((a , b) , _) ((c , d) , _) =
  min-ℚ (min-ℚ (a *ℚ c) (a *ℚ d)) (min-ℚ (b *ℚ c) (b *ℚ d))

upper-bound-mul-interval-ℚ : interval-ℚ → interval-ℚ → ℚ
upper-bound-mul-interval-ℚ ((a , b) , _) ((c , d) , _) =
  max-ℚ (max-ℚ (a *ℚ c) (a *ℚ d)) (max-ℚ (b *ℚ c) (b *ℚ d))

abstract
  lower-bound-leq-upper-bound-mul-interval-ℚ :
    ([a,b] [c,d] : interval-ℚ) →
    leq-ℚ
      ( lower-bound-mul-interval-ℚ [a,b] [c,d])
      ( upper-bound-mul-interval-ℚ [a,b] [c,d])
  lower-bound-leq-upper-bound-mul-interval-ℚ ((a , b) , _) ((c , d) , _) =
    let min≤max = min-leq-max-Decidable-Total-Order ℚ-Decidable-Total-Order
    in
      transitive-leq-ℚ
        ( min-ℚ (min-ℚ (a *ℚ c) (a *ℚ d)) (min-ℚ (b *ℚ c) (b *ℚ d)))
        ( max-ℚ (min-ℚ (a *ℚ c) (a *ℚ d)) (min-ℚ (b *ℚ c) (b *ℚ d)))
        ( max-ℚ (max-ℚ (a *ℚ c) (a *ℚ d)) (max-ℚ (b *ℚ c) (b *ℚ d)))
        ( max-leq-leq-ℚ _ _ _ _ (min≤max _ _) (min≤max _ _))
        ( min≤max _ _)

mul-interval-ℚ : interval-ℚ → interval-ℚ → interval-ℚ
mul-interval-ℚ [a,b] [c,d] =
  ( ( lower-bound-mul-interval-ℚ [a,b] [c,d] ,
      upper-bound-mul-interval-ℚ [a,b] [c,d]) ,
    lower-bound-leq-upper-bound-mul-interval-ℚ [a,b] [c,d])
```

## Properties

### Left multiplication by an interval

#### By a negative rational number

```agda
left-mul-interval-ℚ⁻ : interval-ℚ → ℚ⁻ → interval-ℚ
left-mul-interval-ℚ⁻ ((p , q) , p≤q) s⁻@(s , _) =
  ((q *ℚ s , p *ℚ s) , reverses-leq-right-mul-ℚ⁻ s⁻ _ _ p≤q)

abstract
  left-mul-element-interval-ℚ⁻ :
    ([p,q] : interval-ℚ) → (r : ℚ⁻) → (s : ℚ) → is-in-interval-ℚ [p,q] s →
    is-in-interval-ℚ
      ( left-mul-interval-ℚ⁻ [p,q] r)
      ( s *ℚ rational-ℚ⁻ r)
  left-mul-element-interval-ℚ⁻
    ((p , q) , p≤q) r s (p≤s , s≤q) =
      ( reverses-leq-right-mul-ℚ⁻ r _ _ s≤q ,
        reverses-leq-right-mul-ℚ⁻ r _ _ p≤s)

  image-left-mul-element-interval-ℚ⁻ :
    ([p,q] : interval-ℚ) → (r : ℚ⁻) → (s : ℚ) →
    is-in-interval-ℚ
      ( left-mul-interval-ℚ⁻ [p,q] r)
      ( s) →
    is-in-im-subtype (mul-ℚ' (rational-ℚ⁻ r)) (subtype-interval-ℚ [p,q]) s
  image-left-mul-element-interval-ℚ⁻
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

  is-interval-map-left-mul-ℚ⁻ :
    (q : ℚ⁻) ([a,b] : interval-ℚ) →
    is-interval-map-ℚ
      ( mul-ℚ' (rational-ℚ⁻ q))
      ( [a,b])
      ( left-mul-interval-ℚ⁻ [a,b] q)
  is-interval-map-left-mul-ℚ⁻ q [a,b] =
    ( ind-Σ (left-mul-element-interval-ℚ⁻ [a,b] q) ,
      ind-Σ (image-left-mul-element-interval-ℚ⁻ [a,b] q))
```

#### By a positive rational number

```agda
left-mul-interval-ℚ⁺ : interval-ℚ → ℚ⁺ → interval-ℚ
left-mul-interval-ℚ⁺ ((p , q) , p≤q) s⁺@(s , _) =
  ((p *ℚ s , q *ℚ s) , preserves-leq-right-mul-ℚ⁺ s⁺ _ _ p≤q)

abstract
  left-mul-element-interval-ℚ⁺ :
    ([p,q] : interval-ℚ) → (r : ℚ⁺) → (s : ℚ) → is-in-interval-ℚ [p,q] s →
    is-in-interval-ℚ
      ( left-mul-interval-ℚ⁺ [p,q] r)
      ( s *ℚ rational-ℚ⁺ r)
  left-mul-element-interval-ℚ⁺
    ((p , q) , p≤q) r s (p≤s , s≤q) =
      ( preserves-leq-right-mul-ℚ⁺ r _ _ p≤s ,
        preserves-leq-right-mul-ℚ⁺ r _ _ s≤q)

  image-left-mul-element-interval-ℚ⁺ :
    ([p,q] : interval-ℚ) → (r : ℚ⁺) → (s : ℚ) →
    is-in-interval-ℚ
      ( left-mul-interval-ℚ⁺ [p,q] r)
      ( s) →
    is-in-im-subtype (mul-ℚ' (rational-ℚ⁺ r)) (subtype-interval-ℚ [p,q]) s
  image-left-mul-element-interval-ℚ⁺
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

  is-interval-map-left-mul-ℚ⁺ :
    (q : ℚ⁺) ([a,b] : interval-ℚ) →
    is-interval-map-ℚ
      ( mul-ℚ' (rational-ℚ⁺ q))
      ( [a,b])
      ( left-mul-interval-ℚ⁺ [a,b] q)
  is-interval-map-left-mul-ℚ⁺ q [a,b] =
    ( ind-Σ (left-mul-element-interval-ℚ⁺ [a,b] q) ,
      ind-Σ (image-left-mul-element-interval-ℚ⁺ [a,b] q))
```

#### By zero

```agda
abstract
  image-left-mul-element-interval-zero-ℚ :
    ([p,q] : interval-ℚ) → (s : ℚ) →
    is-in-interval-ℚ
      ( zero-zero-interval-ℚ)
      ( s) →
    is-in-im-subtype (mul-ℚ' zero-ℚ) (subtype-interval-ℚ [p,q]) s
  image-left-mul-element-interval-zero-ℚ
    ((p , q) , p≤q) s (0≤s , s≤0) =
      intro-exists
        ( p , refl-leq-ℚ p , p≤q)
        ( right-zero-law-mul-ℚ p ∙ antisymmetric-leq-ℚ _ _ 0≤s s≤0)

  is-interval-map-left-mul-zero-ℚ :
    ([a,b] : interval-ℚ) →
    is-interval-map-ℚ
      ( mul-ℚ' zero-ℚ)
      ( [a,b])
      ( zero-zero-interval-ℚ)
  is-interval-map-left-mul-zero-ℚ [a,b] =
    ( ( λ r →
        inv-tr
          ( is-in-interval-ℚ zero-zero-interval-ℚ)
          ( right-zero-law-mul-ℚ _)
          ( refl-leq-ℚ zero-ℚ , refl-leq-ℚ zero-ℚ)) ,
      ind-Σ (image-left-mul-element-interval-zero-ℚ [a,b]))
```

#### By any rational number

```agda
left-mul-interval-ℚ : interval-ℚ → ℚ → interval-ℚ
left-mul-interval-ℚ ((a , b) , a≤b) c =
  ( (min-ℚ (a *ℚ c) (b *ℚ c) , max-ℚ (a *ℚ c) (b *ℚ c)) ,
    min-leq-max-Decidable-Total-Order ℚ-Decidable-Total-Order _ _)

abstract
  left-mul-interval-is-negative-ℚ :
    ([p,q] : interval-ℚ) (r : ℚ) (neg-r : is-negative-ℚ r) →
    left-mul-interval-ℚ [p,q] r ＝
    left-mul-interval-ℚ⁻ [p,q] (r , neg-r)
  left-mul-interval-is-negative-ℚ [p,q]@((p , q) , p≤q) r neg-r =
    unordered-interval-leq-ℚ' _ _
      ( reverses-leq-right-mul-ℚ⁻ (r , neg-r) _ _ p≤q)

  left-mul-interval-is-positive-ℚ :
    ([p,q] : interval-ℚ) (r : ℚ) (pos-r : is-positive-ℚ r) →
    left-mul-interval-ℚ [p,q] r ＝
    left-mul-interval-ℚ⁺ [p,q] (r , pos-r)
  left-mul-interval-is-positive-ℚ [p,q]@((p , q) , p≤q) r pos-r =
    unordered-interval-leq-ℚ _ _
      ( preserves-leq-right-mul-ℚ⁺ (r , pos-r) _ _ p≤q)

  left-mul-interval-is-zero-ℚ :
    ([p,q] : interval-ℚ) (r : ℚ) (is-zero-r : is-zero-ℚ r) →
    left-mul-interval-ℚ [p,q] r ＝ zero-zero-interval-ℚ
  left-mul-interval-is-zero-ℚ ((p , q) , p≤q) _ refl =
    eq-interval-ℚ _ _
      ( ap-min-ℚ
        ( right-zero-law-mul-ℚ _)
        ( right-zero-law-mul-ℚ _) ∙
        idempotent-min-ℚ zero-ℚ)
      ( ap-max-ℚ
        ( right-zero-law-mul-ℚ _)
        ( right-zero-law-mul-ℚ _) ∙
        idempotent-max-ℚ zero-ℚ)

  left-mul-element-interval-ℚ :
    ([p,q] : interval-ℚ) → (r s : ℚ) → is-in-interval-ℚ [p,q] s →
    is-in-interval-ℚ
      ( left-mul-interval-ℚ [p,q] r)
      ( s *ℚ r)
  left-mul-element-interval-ℚ [p,q] r s s∈[p,q] =
    trichotomy-sign-ℚ r
      ( λ neg-r →
        inv-tr
          ( λ [x,y] → is-in-interval-ℚ [x,y] (s *ℚ r))
          ( left-mul-interval-is-negative-ℚ [p,q] r neg-r)
          ( left-mul-element-interval-ℚ⁻ [p,q] (r , neg-r) s s∈[p,q]))
      ( λ r=0 →
        binary-tr
          ( is-in-interval-ℚ)
          ( inv (left-mul-interval-is-zero-ℚ [p,q] r r=0))
          ( inv (ap-mul-ℚ refl r=0 ∙ right-zero-law-mul-ℚ s))
          ( refl-leq-ℚ zero-ℚ , refl-leq-ℚ zero-ℚ))
      ( λ pos-r →
        inv-tr
          ( λ [x,y] → is-in-interval-ℚ [x,y] (s *ℚ r))
          ( left-mul-interval-is-positive-ℚ [p,q] r pos-r)
          ( left-mul-element-interval-ℚ⁺ [p,q] (r , pos-r) s s∈[p,q]))

  image-left-mul-element-interval-ℚ :
    ([p,q] : interval-ℚ) (r s : ℚ) →
    is-in-interval-ℚ
      ( left-mul-interval-ℚ [p,q] r)
      ( s) →
    is-in-im-subtype (mul-ℚ' r) (subtype-interval-ℚ [p,q]) s
  image-left-mul-element-interval-ℚ [p,q] r s s∈[min-pr-qr,max-pr-qr] =
      trichotomy-sign-ℚ r
        ( λ neg-r →
          image-left-mul-element-interval-ℚ⁻
            ( [p,q])
            ( r , neg-r)
            ( s)
            ( tr
              ( λ [x,y] → is-in-interval-ℚ [x,y] s)
              ( left-mul-interval-is-negative-ℚ [p,q] r neg-r)
              ( s∈[min-pr-qr,max-pr-qr])))
        ( λ r=0 →
          inv-tr
            ( λ t → is-in-im-subtype (mul-ℚ' t) (subtype-interval-ℚ [p,q]) s)
            ( r=0)
            ( image-left-mul-element-interval-zero-ℚ
              ( [p,q])
              ( s)
              ( tr
                ( λ [x,y] → is-in-interval-ℚ [x,y] s)
                ( left-mul-interval-is-zero-ℚ [p,q] r r=0)
                ( s∈[min-pr-qr,max-pr-qr]))))
        ( λ pos-r →
          image-left-mul-element-interval-ℚ⁺
            ( [p,q])
            ( r , pos-r)
            ( s)
            ( tr
              ( λ [x,y] → is-in-interval-ℚ [x,y] s)
              ( left-mul-interval-is-positive-ℚ [p,q] r pos-r)
              ( s∈[min-pr-qr,max-pr-qr])))

  is-interval-map-left-mul-ℚ :
    (q : ℚ) ([a,b] : interval-ℚ) →
    is-interval-map-ℚ (mul-ℚ' q) [a,b] (left-mul-interval-ℚ [a,b] q)
  is-interval-map-left-mul-ℚ q [a,b] =
    ( ind-Σ (left-mul-element-interval-ℚ [a,b] q) ,
      ind-Σ (image-left-mul-element-interval-ℚ [a,b] q))
```

### Right multiplication by an interval

```agda
right-mul-interval-ℚ : ℚ → interval-ℚ → interval-ℚ
right-mul-interval-ℚ a ((b , c) , b≤c) =
  ( (min-ℚ (a *ℚ b) (a *ℚ c) , max-ℚ (a *ℚ b) (a *ℚ c)) ,
    min-leq-max-Decidable-Total-Order ℚ-Decidable-Total-Order _ _)

abstract
  commute-left-right-mul-interval-ℚ :
    ([p,q] : interval-ℚ) (r : ℚ) →
    left-mul-interval-ℚ [p,q] r ＝ right-mul-interval-ℚ r [p,q]
  commute-left-right-mul-interval-ℚ [p,q] r =
    eq-interval-ℚ _ _
      ( ap-min-ℚ (commutative-mul-ℚ _ _) (commutative-mul-ℚ _ _))
      ( ap-max-ℚ (commutative-mul-ℚ _ _) (commutative-mul-ℚ _ _))

  right-mul-element-interval-ℚ :
    ([p,q] : interval-ℚ) → (r s : ℚ) → is-in-interval-ℚ [p,q] s →
    is-in-interval-ℚ
      ( right-mul-interval-ℚ r [p,q])
      ( r *ℚ s)
  right-mul-element-interval-ℚ [p,q] r s s∈[p,q] =
    binary-tr
      ( is-in-interval-ℚ)
      ( commute-left-right-mul-interval-ℚ [p,q] r)
      ( commutative-mul-ℚ s r)
      ( left-mul-element-interval-ℚ [p,q] r s s∈[p,q])

  image-right-mul-element-interval-ℚ :
    ([p,q] : interval-ℚ) (r s : ℚ) →
    is-in-interval-ℚ
      ( right-mul-interval-ℚ r [p,q])
      ( s) →
    is-in-im-subtype (mul-ℚ r) (subtype-interval-ℚ [p,q]) s
  image-right-mul-element-interval-ℚ [p,q] r s s∈[min-rp-rq,max-rp-rq] =
    tr
      ( λ f → is-in-im-subtype f (subtype-interval-ℚ [p,q]) s)
      ( eq-htpy (λ _ → commutative-mul-ℚ _ _))
      ( image-left-mul-element-interval-ℚ [p,q] r s
        ( inv-tr
          ( λ [x,y] → is-in-interval-ℚ [x,y] s)
          ( commute-left-right-mul-interval-ℚ [p,q] r)
          ( s∈[min-rp-rq,max-rp-rq])))

  is-interval-map-right-mul-ℚ :
    (q : ℚ) ([a,b] : interval-ℚ) →
    is-interval-map-ℚ (mul-ℚ q) [a,b] (right-mul-interval-ℚ q [a,b])
  is-interval-map-right-mul-ℚ q [a,b] =
    binary-tr
      ( λ f i → is-interval-map-ℚ f [a,b] i)
      ( eq-htpy (λ _ → commutative-mul-ℚ _ _))
      ( commute-left-right-mul-interval-ℚ [a,b] q)
      ( is-interval-map-left-mul-ℚ q [a,b])
```

### Multiplication of two closed intervals

```agda
abstract
  mul-elements-intervals-ℚ :
    ([a,b] [c,d] : interval-ℚ) (p q : ℚ) →
    is-in-interval-ℚ [a,b] p → is-in-interval-ℚ [c,d] q →
    is-in-interval-ℚ (mul-interval-ℚ [a,b] [c,d]) (p *ℚ q)
  mul-elements-intervals-ℚ
    [a,b]@((a , b) , a≤b) [c,d]@((c , d) , c≤d) p q
    p∈[a,b]@(a≤p , p≤b) q∈[c,d]@(c≤q , q≤d) =
      let
        (min-aq-bq≤pq , pq≤max-aq-bq) =
          left-mul-element-interval-ℚ [a,b] q p p∈[a,b]
        (min-ac-ad≤aq , aq≤max-ac-ad) =
          right-mul-element-interval-ℚ [c,d] a q q∈[c,d]
        (min-bc-bd≤bq , bq≤max-bc-bd) =
          right-mul-element-interval-ℚ [c,d] b q q∈[c,d]
      in
        ( transitive-leq-ℚ
            ( lower-bound-mul-interval-ℚ [a,b] [c,d])
            ( _)
            ( p *ℚ q)
            ( min-aq-bq≤pq)
            ( min-leq-leq-ℚ _ _ _ _ min-ac-ad≤aq min-bc-bd≤bq) ,
          transitive-leq-ℚ
            ( p *ℚ q)
            ( _)
            ( upper-bound-mul-interval-ℚ [a,b] [c,d])
            ( max-leq-leq-ℚ _ _ _ _ aq≤max-ac-ad bq≤max-bc-bd)
            ( pq≤max-aq-bq))

  image-mul-elements-intervals-ℚ :
    ([a,b] [c,d] : interval-ℚ) → (q : ℚ) →
    is-in-interval-ℚ (mul-interval-ℚ [a,b] [c,d]) q →
    is-in-subtype
      ( minkowski-mul-Commutative-Monoid
        ( commutative-monoid-mul-ℚ)
        ( subtype-interval-ℚ [a,b])
        ( subtype-interval-ℚ [c,d]))
      ( q)
  image-mul-elements-intervals-ℚ
    [a,b]@((a , b) , a≤b) [c,d]@((c , d) , c≤d) q
    (min-ac-ad-bc-bd≤q , q≤max-ac-ad-bc-bd) =
      let
        motive =
          minkowski-mul-Commutative-Monoid
            ( commutative-monoid-mul-ℚ)
            ( subtype-interval-ℚ [a,b])
            ( subtype-interval-ℚ [c,d])
            ( q)
        from-[a,b] :
          (x : ℚ) → is-in-interval-ℚ [a,b] x →
          is-in-im-subtype (mul-ℚ x) (subtype-interval-ℚ [c,d]) q →
          type-Prop motive
        from-[a,b] x x∈[a,b] q∈p[c,d] =
          let open do-syntax-trunc-Prop motive
          in do
            ((y , y∈[c,d]) , xy=q) ← q∈p[c,d]
            intro-exists (x , y) (x∈[a,b] , y∈[c,d] , inv xy=q)
        from-[c,d] :
          (y : ℚ) → is-in-interval-ℚ [c,d] y →
          is-in-im-subtype (mul-ℚ' y) (subtype-interval-ℚ [a,b]) q →
          type-Prop motive
        from-[c,d] y y∈[c,d] q∈[a,b]y =
          let open do-syntax-trunc-Prop motive
          in do
            ((x , x∈[a,b]) , xy=q) ← q∈[a,b]y
            intro-exists (x , y) (x∈[a,b] , y∈[c,d] , inv xy=q)
      in
        {!   !}
```
