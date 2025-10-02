# Addition on closed intervals in the rational numbers

```agda
module elementary-number-theory.addition-closed-intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.closed-intervals-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.poset-closed-intervals-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.binary-transport
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

Given two
[closed intervals](elementary-number-theory.closed-intervals-rational-numbers.md)
`[a, b]` and `[c, d]` in the
[rational numbers](elementary-number-theory.rational-numbers.md), the
[Minkowski sum](group-theory.minkowski-multiplication-commutative-monoids.md) of
those intervals (interpreted as [subtypes](foundation.subtypes.md) of `ℚ`)
agrees with the interval `[a + c, b + d]`.

## Definition

```agda
add-closed-interval-ℚ :
  closed-interval-ℚ → closed-interval-ℚ →
  closed-interval-ℚ
add-closed-interval-ℚ ((a , b) , a≤b) ((c , d) , c≤d) =
  ((a +ℚ c , b +ℚ d) , preserves-leq-add-ℚ a≤b c≤d)
```

## Properties

### Agreement with the Minkowski sum

```agda
abstract
  is-in-minkowski-sum-is-in-add-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    (q : ℚ) →
    is-in-closed-interval-ℚ
      ( add-closed-interval-ℚ [a,b] [c,d])
      ( q) →
    is-in-subtype
      ( minkowski-mul-Commutative-Monoid
        ( commutative-monoid-add-ℚ)
        ( subtype-closed-interval-ℚ [a,b])
        ( subtype-closed-interval-ℚ [c,d]))
      ( q)
  is-in-minkowski-sum-is-in-add-closed-interval-ℚ
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

  is-in-add-interval-add-is-in-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) (s t : ℚ) →
    is-in-closed-interval-ℚ [a,b] s → is-in-closed-interval-ℚ [c,d] t →
    is-in-closed-interval-ℚ (add-closed-interval-ℚ [a,b] [c,d]) (s +ℚ t)
  is-in-add-interval-add-is-in-closed-interval-ℚ
    ((a , b) , _) ((c , d) , _) s t (a≤s , s≤b) (c≤t , t≤d) =
    ( preserves-leq-add-ℚ a≤s c≤t ,
      preserves-leq-add-ℚ s≤b t≤d)

  is-in-add-interval-is-in-minkowski-sum-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    (q : ℚ) →
    is-in-subtype
      ( minkowski-mul-Commutative-Monoid
        ( commutative-monoid-add-ℚ)
        ( subtype-closed-interval-ℚ [a,b])
        ( subtype-closed-interval-ℚ [c,d]))
      ( q) →
    is-in-closed-interval-ℚ
      ( add-closed-interval-ℚ [a,b] [c,d])
      ( q)
  is-in-add-interval-is-in-minkowski-sum-ℚ
    [a,b] [c,d] q q∈[a,b]+[c,d] =
      let
        open
          do-syntax-trunc-Prop
            ( subtype-closed-interval-ℚ (add-closed-interval-ℚ [a,b] [c,d]) q)
      in do
        ((s , t) , s∈[a,b] , t∈[c,d] , q=s+t) ← q∈[a,b]+[c,d]
        inv-tr
          ( is-in-closed-interval-ℚ (add-closed-interval-ℚ [a,b] [c,d]))
          ( q=s+t)
          ( is-in-add-interval-add-is-in-closed-interval-ℚ [a,b] [c,d] s t
            ( s∈[a,b])
            ( t∈[c,d]))

has-same-elements-minkowski-add-closed-interval-ℚ :
  ([a,b] [c,d] : closed-interval-ℚ) →
  has-same-elements-subtype
    ( minkowski-mul-Commutative-Monoid
      ( commutative-monoid-add-ℚ)
      ( subtype-closed-interval-ℚ [a,b])
      ( subtype-closed-interval-ℚ [c,d]))
    ( subtype-closed-interval-ℚ
      ( add-closed-interval-ℚ [a,b] [c,d]))
has-same-elements-minkowski-add-closed-interval-ℚ [a,b] [c,d] q =
  ( is-in-add-interval-is-in-minkowski-sum-ℚ [a,b] [c,d] q ,
    is-in-minkowski-sum-is-in-add-closed-interval-ℚ [a,b] [c,d] q)

eq-minkowski-add-closed-interval-ℚ :
  ([a,b] [c,d] : closed-interval-ℚ) →
  minkowski-mul-Commutative-Monoid
    ( commutative-monoid-add-ℚ)
    ( subtype-closed-interval-ℚ [a,b])
    ( subtype-closed-interval-ℚ [c,d]) ＝
  subtype-closed-interval-ℚ
    ( add-closed-interval-ℚ [a,b] [c,d])
eq-minkowski-add-closed-interval-ℚ [a,b] [c,d] =
  eq-has-same-elements-subtype _ _
    ( has-same-elements-minkowski-add-closed-interval-ℚ [a,b] [c,d])
```

### Associativity

```agda
abstract
  associative-add-closed-interval-ℚ :
    ([a,b] [c,d] [e,f] : closed-interval-ℚ) →
    add-closed-interval-ℚ
      ( add-closed-interval-ℚ [a,b] [c,d])
      ( [e,f]) ＝
    add-closed-interval-ℚ
      ( [a,b])
      ( add-closed-interval-ℚ [c,d] [e,f])
  associative-add-closed-interval-ℚ _ _ _ =
    eq-closed-interval-ℚ _ _
      ( associative-add-ℚ _ _ _)
      ( associative-add-ℚ _ _ _)
```

### Commutativity

```agda
abstract
  commutative-add-closed-interval-ℚ :
    ([a,b] [c,d] : closed-interval-ℚ) →
    add-closed-interval-ℚ [a,b] [c,d] ＝
    add-closed-interval-ℚ [c,d] [a,b]
  commutative-add-closed-interval-ℚ _ _ =
    eq-closed-interval-ℚ _ _
      ( commutative-add-ℚ _ _)
      ( commutative-add-ℚ _ _)
```

### Unit laws

```agda
abstract
  left-unit-law-add-closed-interval-ℚ :
    ([a,b] : closed-interval-ℚ) →
    add-closed-interval-ℚ
      ( zero-zero-closed-interval-ℚ)
      ( [a,b]) ＝
    [a,b]
  left-unit-law-add-closed-interval-ℚ _ =
    eq-closed-interval-ℚ _ _
      ( left-unit-law-add-ℚ _)
      ( left-unit-law-add-ℚ _)

  right-unit-law-add-closed-interval-ℚ :
    ([a,b] : closed-interval-ℚ) →
    add-closed-interval-ℚ
      ( [a,b])
      ( zero-zero-closed-interval-ℚ) ＝
    [a,b]
  right-unit-law-add-closed-interval-ℚ _ =
    eq-closed-interval-ℚ _ _
      ( right-unit-law-add-ℚ _)
      ( right-unit-law-add-ℚ _)
```

### The commutative monoid of addition of rational intervals

```agda
semigroup-add-closed-interval-ℚ : Semigroup lzero
semigroup-add-closed-interval-ℚ =
  ( set-closed-interval-ℚ ,
    add-closed-interval-ℚ ,
    associative-add-closed-interval-ℚ)

monoid-add-closed-interval-ℚ : Monoid lzero
monoid-add-closed-interval-ℚ =
  ( semigroup-add-closed-interval-ℚ ,
    zero-zero-closed-interval-ℚ ,
    left-unit-law-add-closed-interval-ℚ ,
    right-unit-law-add-closed-interval-ℚ)

commutative-monoid-add-closed-interval-ℚ : Commutative-Monoid lzero
commutative-monoid-add-closed-interval-ℚ =
  ( monoid-add-closed-interval-ℚ ,
    commutative-add-closed-interval-ℚ)
```

### Containment on rational intervals is preserved by addition

```agda
abstract
  preserves-leq-left-add-closed-interval-ℚ :
    ([c,d] [a,b] [a',b'] : closed-interval-ℚ) →
    leq-closed-interval-ℚ [a,b] [a',b'] →
    leq-closed-interval-ℚ
      ( add-closed-interval-ℚ [a,b] [c,d])
      ( add-closed-interval-ℚ [a',b'] [c,d])
  preserves-leq-left-add-closed-interval-ℚ
    ((c , d) , _) ((a , b) , _) ((a' , b') , _) (a'≤a , b≤b') =
    ( preserves-leq-left-add-ℚ c a' a a'≤a ,
      preserves-leq-left-add-ℚ d b b' b≤b')

  preserves-leq-right-add-closed-interval-ℚ :
    ([a,b] [c,d] [c',d'] : closed-interval-ℚ) →
    leq-closed-interval-ℚ [c,d] [c',d'] →
    leq-closed-interval-ℚ
      ( add-closed-interval-ℚ [a,b] [c,d])
      ( add-closed-interval-ℚ [a,b] [c',d'])
  preserves-leq-right-add-closed-interval-ℚ [a,b] [c,d] [c',d'] [c,d]⊆[c',d'] =
    binary-tr
      ( leq-closed-interval-ℚ)
      ( commutative-add-closed-interval-ℚ [c,d] [a,b])
      ( commutative-add-closed-interval-ℚ [c',d'] [a,b])
      ( preserves-leq-left-add-closed-interval-ℚ
        ( [a,b])
        ( [c,d])
        ( [c',d'])
        ( [c,d]⊆[c',d']))

  preserves-leq-add-closed-interval-ℚ :
    ([a,b] [a',b'] [c,d] [c',d'] : closed-interval-ℚ) →
    leq-closed-interval-ℚ [a,b] [a',b'] → leq-closed-interval-ℚ [c,d] [c',d'] →
    leq-closed-interval-ℚ
      ( add-closed-interval-ℚ [a,b] [c,d])
      ( add-closed-interval-ℚ [a',b'] [c',d'])
  preserves-leq-add-closed-interval-ℚ
    [a,b] [a',b'] [c,d] [c',d'] [a,b]⊆[a',b'] [c,d]⊆[c',d'] =
    transitive-leq-closed-interval-ℚ
      ( add-closed-interval-ℚ [a,b] [c,d])
      ( add-closed-interval-ℚ [a,b] [c',d'])
      ( add-closed-interval-ℚ [a',b'] [c',d'])
      ( preserves-leq-left-add-closed-interval-ℚ
        ( [c',d'])
        ( [a,b])
        ( [a',b'])
        ( [a,b]⊆[a',b']))
      ( preserves-leq-right-add-closed-interval-ℚ
        ( [a,b])
        ( [c,d])
        ( [c',d'])
        ( [c,d]⊆[c',d']))
```
