# Addition on closed intervals in the rational numbers

```agda
module elementary-number-theory.addition-inhabited-closed-intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.inhabited-closed-intervals-rational-numbers
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

open import order-theory.inhabited-closed-intervals-posets
```

</details>

## Idea

Given two
[inhabited closed intervals](elementary-number-theory.inhabited-closed-intervals-rational-numbers.md)
`[a, b]` and `[c, d]` in the
[rational numbers](elementary-number-theory.rational-numbers.md), the
[Minkowski sum](group-theory.minkowski-multiplication-commutative-monoids.md) of
those intervals (interpreted as [subtypes](foundation.subtypes.md) of `ℚ`)
agrees with the interval `[a + c, b + d]`.

## Definition

```agda
add-inhabited-closed-interval-ℚ :
  inhabited-closed-interval-ℚ → inhabited-closed-interval-ℚ →
  inhabited-closed-interval-ℚ
add-inhabited-closed-interval-ℚ ((a , b) , a≤b) ((c , d) , c≤d) =
  ((a +ℚ c , b +ℚ d) , preserves-leq-add-ℚ a≤b c≤d)
```

## Properties

### Agreement with the Minkowski sum

```agda
abstract
  is-in-minkowski-sum-is-in-add-inhabited-closed-interval-ℚ :
    ([a,b] [c,d] : inhabited-closed-interval-ℚ) →
    (q : ℚ) →
    is-in-inhabited-closed-interval-ℚ
      ( add-inhabited-closed-interval-ℚ [a,b] [c,d])
      ( q) →
    is-in-subtype
      ( minkowski-mul-Commutative-Monoid
        ( commutative-monoid-add-ℚ)
        ( subtype-inhabited-closed-interval-ℚ [a,b])
        ( subtype-inhabited-closed-interval-ℚ [c,d]))
      ( q)
  is-in-minkowski-sum-is-in-add-inhabited-closed-interval-ℚ
    [a,b]@((a , b) , a≤b) [c,d]@((c , d) , c≤d) q (a+c≤q , q≤b+d) =
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

  is-in-add-interval-is-in-minkowski-sum-ℚ :
    ([a,b] [c,d] : inhabited-closed-interval-ℚ) →
    (q : ℚ) →
    is-in-subtype
      ( minkowski-mul-Commutative-Monoid
        ( commutative-monoid-add-ℚ)
        ( subtype-inhabited-closed-interval-ℚ [a,b])
        ( subtype-inhabited-closed-interval-ℚ [c,d]))
      ( q) →
    is-in-inhabited-closed-interval-ℚ
      ( add-inhabited-closed-interval-ℚ [a,b] [c,d])
      ( q)
  is-in-add-interval-is-in-minkowski-sum-ℚ
    [a,b]@((a , b) , a≤b) [c,d]@((c , d) , c≤d) q q∈[a,b]+[c,d] =
      let
        open
          do-syntax-trunc-Prop
            ( subtype-inhabited-closed-interval-ℚ
              ( add-inhabited-closed-interval-ℚ [a,b] [c,d])
              ( q))
      in do
        ((s , t) , (a≤s , s≤b) , (c≤t , t≤d) , q=s+t) ← q∈[a,b]+[c,d]
        ( inv-tr (leq-ℚ (a +ℚ c)) q=s+t (preserves-leq-add-ℚ a≤s c≤t) ,
          inv-tr (λ r → leq-ℚ r (b +ℚ d)) q=s+t (preserves-leq-add-ℚ s≤b t≤d))

has-same-elements-minkowski-add-inhabited-closed-interval-ℚ :
  ([a,b] [c,d] : inhabited-closed-interval-ℚ) →
  has-same-elements-subtype
    ( minkowski-mul-Commutative-Monoid
      ( commutative-monoid-add-ℚ)
      ( subtype-inhabited-closed-interval-ℚ [a,b])
      ( subtype-inhabited-closed-interval-ℚ [c,d]))
    ( subtype-inhabited-closed-interval-ℚ
      ( add-inhabited-closed-interval-ℚ [a,b] [c,d]))
has-same-elements-minkowski-add-inhabited-closed-interval-ℚ [a,b] [c,d] q =
  ( is-in-add-interval-is-in-minkowski-sum-ℚ [a,b] [c,d] q ,
    is-in-minkowski-sum-is-in-add-inhabited-closed-interval-ℚ [a,b] [c,d] q)

eq-minkowski-add-inhabited-closed-interval-ℚ :
  ([a,b] [c,d] : inhabited-closed-interval-ℚ) →
  minkowski-mul-Commutative-Monoid
    ( commutative-monoid-add-ℚ)
    ( subtype-inhabited-closed-interval-ℚ [a,b])
    ( subtype-inhabited-closed-interval-ℚ [c,d]) ＝
  subtype-inhabited-closed-interval-ℚ
    ( add-inhabited-closed-interval-ℚ [a,b] [c,d])
eq-minkowski-add-inhabited-closed-interval-ℚ [a,b] [c,d] =
  eq-has-same-elements-subtype _ _
    ( has-same-elements-minkowski-add-inhabited-closed-interval-ℚ [a,b] [c,d])
```

### Associativity

```agda
abstract
  associative-add-inhabited-closed-interval-ℚ :
    ([a,b] [c,d] [e,f] : inhabited-closed-interval-ℚ) →
    add-inhabited-closed-interval-ℚ
      ( add-inhabited-closed-interval-ℚ [a,b] [c,d])
      ( [e,f]) ＝
    add-inhabited-closed-interval-ℚ
      ( [a,b])
      ( add-inhabited-closed-interval-ℚ [c,d] [e,f])
  associative-add-inhabited-closed-interval-ℚ _ _ _ =
    eq-inhabited-closed-interval-ℚ _ _
      ( associative-add-ℚ _ _ _)
      ( associative-add-ℚ _ _ _)
```

### Commutativity

```agda
abstract
  commutative-add-inhabited-closed-interval-ℚ :
    ([a,b] [c,d] : inhabited-closed-interval-ℚ) →
    add-inhabited-closed-interval-ℚ [a,b] [c,d] ＝
    add-inhabited-closed-interval-ℚ [c,d] [a,b]
  commutative-add-inhabited-closed-interval-ℚ _ _ =
    eq-inhabited-closed-interval-ℚ _ _
      ( commutative-add-ℚ _ _)
      ( commutative-add-ℚ _ _)
```

### Unit laws

```agda
abstract
  left-unit-law-add-inhabited-closed-interval-ℚ :
    ([a,b] : inhabited-closed-interval-ℚ) →
    add-inhabited-closed-interval-ℚ
      ( zero-zero-inhabited-closed-interval-ℚ)
      ( [a,b]) ＝
    [a,b]
  left-unit-law-add-inhabited-closed-interval-ℚ _ =
    eq-inhabited-closed-interval-ℚ _ _
      ( left-unit-law-add-ℚ _)
      ( left-unit-law-add-ℚ _)

  right-unit-law-add-inhabited-closed-interval-ℚ :
    ([a,b] : inhabited-closed-interval-ℚ) →
    add-inhabited-closed-interval-ℚ
      ( [a,b])
      ( zero-zero-inhabited-closed-interval-ℚ) ＝
    [a,b]
  right-unit-law-add-inhabited-closed-interval-ℚ _ =
    eq-inhabited-closed-interval-ℚ _ _
      ( right-unit-law-add-ℚ _)
      ( right-unit-law-add-ℚ _)
```

### The commutative monoid of addition of rational intervals

```agda
semigroup-add-inhabited-closed-interval-ℚ : Semigroup lzero
semigroup-add-inhabited-closed-interval-ℚ =
  ( set-inhabited-closed-interval-ℚ ,
    add-inhabited-closed-interval-ℚ ,
    associative-add-inhabited-closed-interval-ℚ)

monoid-add-inhabited-closed-interval-ℚ : Monoid lzero
monoid-add-inhabited-closed-interval-ℚ =
  ( semigroup-add-inhabited-closed-interval-ℚ ,
    zero-zero-inhabited-closed-interval-ℚ ,
    left-unit-law-add-inhabited-closed-interval-ℚ ,
    right-unit-law-add-inhabited-closed-interval-ℚ)

commutative-monoid-add-inhabited-closed-interval-ℚ : Commutative-Monoid lzero
commutative-monoid-add-inhabited-closed-interval-ℚ =
  ( monoid-add-inhabited-closed-interval-ℚ ,
    commutative-add-inhabited-closed-interval-ℚ)
```
