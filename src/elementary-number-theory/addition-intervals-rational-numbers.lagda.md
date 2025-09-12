# Addition on intervals in the rational numbers

```agda
module elementary-number-theory.addition-intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.intervals-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.minkowski-multiplication-commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups

open import order-theory.closed-intervals-posets
```

</details>

## Idea

Given two [intervals](elementary-number-theory.intervals-rational-numbers.md)
`[a, b]` and `[c, d]` in the
[rational numbers](elementary-number-theory.rational-numbers.md), the
[Minkowski sum](group-theory.minkowski-multiplications-commutative-monoids.md)
of those intervals (interpreted as [subtypes](foundation.subtypes.md) of `ℚ`)
agrees with the interval `[a +ℚ c, b +ℚ d]`.

## Definition

```agda
add-interval-ℚ : interval-ℚ → interval-ℚ → interval-ℚ
add-interval-ℚ ((a , b) , a≤b) ((c , d) , c≤d) =
  ((a +ℚ c , b +ℚ d) , preserves-leq-add-ℚ a≤b c≤d)
```

## Properties

### Agreement with the Minkowski sum

```agda
abstract
  has-same-elements-minkowski-add-interval-ℚ :
    ([a,b] [c,d] : interval-ℚ) →
    has-same-elements-subtype
      ( minkowski-mul-Commutative-Monoid
        ( commutative-monoid-add-ℚ)
        ( subtype-interval-ℚ [a,b])
        ( subtype-interval-ℚ [c,d]))
      ( subtype-interval-ℚ (add-interval-ℚ [a,b] [c,d]))
  pr1
    ( has-same-elements-minkowski-add-interval-ℚ
      [a,b]@((a , b) , a≤b) [c,d]@((c , d) , c≤d) q) q∈[a,b]+[c,d] =
        let
          open
            do-syntax-trunc-Prop
              ( subtype-interval-ℚ (add-interval-ℚ [a,b] [c,d]) q)
        in do
          ((s , t) , (a≤s , s≤b) , (c≤t , t≤d) , q=s+t) ← q∈[a,b]+[c,d]
          ( inv-tr (leq-ℚ (a +ℚ c)) q=s+t (preserves-leq-add-ℚ a≤s c≤t) ,
            inv-tr (λ r → leq-ℚ r (b +ℚ d)) q=s+t (preserves-leq-add-ℚ s≤b t≤d))
  pr2
    ( has-same-elements-minkowski-add-interval-ℚ
      [a,b]@((a , b) , a≤b) [c,d]@((c , d) , c≤d) q) (a+c≤q , q≤b+d) =
        rec-coproduct
          ( λ q≤a+d →
            intro-exists
              ( a , q -ℚ a)
              ( ( refl-leq-ℚ a , a≤b) ,
                ( leq-transpose-left-add-ℚ' _ _ _ a+c≤q ,
                  leq-transpose-right-add-ℚ' _ _ _ q≤a+d) ,
                inv (is-identity-right-conjugation-add-ℚ _ _)))
          ( λ a+d≤q →
            intro-exists
              ( q -ℚ d , d)
              ( ( leq-transpose-left-add-ℚ _ _ _ a+d≤q ,
                  leq-transpose-right-add-ℚ _ _ _ q≤b+d) ,
                ( c≤d , refl-leq-ℚ d) ,
                inv (is-section-diff-ℚ _ _)))
          ( linear-leq-ℚ q (a +ℚ d))

  eq-minkowski-add-interval-ℚ :
    ([a,b] [c,d] : interval-ℚ) →
    minkowski-mul-Commutative-Monoid
      ( commutative-monoid-add-ℚ)
      ( subtype-interval-ℚ [a,b])
      ( subtype-interval-ℚ [c,d]) ＝
    subtype-interval-ℚ (add-interval-ℚ [a,b] [c,d])
  eq-minkowski-add-interval-ℚ [a,b] [c,d] =
    eq-has-same-elements-subtype _ _
      ( has-same-elements-minkowski-add-interval-ℚ [a,b] [c,d])
```

### Associativity

```agda
abstract
  associative-add-interval-ℚ :
    ([a,b] [c,d] [e,f] : interval-ℚ) →
    add-interval-ℚ (add-interval-ℚ [a,b] [c,d]) [e,f] ＝
    add-interval-ℚ [a,b] (add-interval-ℚ [c,d] [e,f])
  associative-add-interval-ℚ _ _ _ =
    eq-interval-ℚ _ _ (associative-add-ℚ _ _ _) (associative-add-ℚ _ _ _)
```

### Commutativity

```agda
abstract
  commutative-add-interval-ℚ :
    ([a,b] [c,d] : interval-ℚ) →
    add-interval-ℚ [a,b] [c,d] ＝ add-interval-ℚ [c,d] [a,b]
  commutative-add-interval-ℚ _ _ =
    eq-interval-ℚ _ _ (commutative-add-ℚ _ _) (commutative-add-ℚ _ _)
```

### Unit laws

```agda
abstract
  left-unit-law-add-interval-ℚ :
    ([a,b] : interval-ℚ) → add-interval-ℚ zero-zero-interval-ℚ [a,b] ＝ [a,b]
  left-unit-law-add-interval-ℚ _ =
    eq-interval-ℚ _ _ (left-unit-law-add-ℚ _) (left-unit-law-add-ℚ _)

  right-unit-law-add-interval-ℚ :
    ([a,b] : interval-ℚ) → add-interval-ℚ [a,b] zero-zero-interval-ℚ ＝ [a,b]
  right-unit-law-add-interval-ℚ _ =
    eq-interval-ℚ _ _ (right-unit-law-add-ℚ _) (right-unit-law-add-ℚ _)
```

### The commutative monoid of addition of rational intervals

```agda
semigroup-add-interval-ℚ : Semigroup lzero
semigroup-add-interval-ℚ =
  ( set-interval-ℚ ,
    add-interval-ℚ ,
    associative-add-interval-ℚ)

monoid-add-interval-ℚ : Monoid lzero
monoid-add-interval-ℚ =
  ( semigroup-add-interval-ℚ ,
    zero-zero-interval-ℚ ,
    left-unit-law-add-interval-ℚ ,
    right-unit-law-add-interval-ℚ)

commutative-monoid-add-interval-ℚ : Commutative-Monoid lzero
commutative-monoid-add-interval-ℚ =
  ( monoid-add-interval-ℚ ,
    commutative-add-interval-ℚ)
```
