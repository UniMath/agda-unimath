# Closed intervals in posets

```agda
module order-theory.closed-intervals-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.images-subtypes
open import foundation.inhabited-subtypes
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.univalence
open import foundation.universe-levels

open import order-theory.interval-subposets
open import order-theory.posets
open import order-theory.subposets
```

</details>

## Idea

A
{{#concept "closed interval" disambiguation="in a poset" Agda=closed-interval-Poset}}
in a poset `P` consists of a pair of elements `x` and `y` in `P` with `x ≤ y`.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  closed-interval-Poset : UU (l1 ⊔ l2)
  closed-interval-Poset =
    Σ (type-Poset X) (λ x → Σ (type-Poset X) ( λ y → leq-Poset X x y))

  lower-bound-closed-interval-Poset : closed-interval-Poset → type-Poset X
  lower-bound-closed-interval-Poset (x , _ , _) = x

  upper-bound-closed-interval-Poset : closed-interval-Poset → type-Poset X
  upper-bound-closed-interval-Poset (_ , y , _) = y

  subposet-closed-interval-Poset : closed-interval-Poset → Subposet l2 X
  subposet-closed-interval-Poset (x , y , _) =
    is-in-interval-Poset X x y

  type-closed-interval-Poset : closed-interval-Poset → UU (l1 ⊔ l2)
  type-closed-interval-Poset [x,y] =
    type-subtype (subposet-closed-interval-Poset [x,y])

  is-in-closed-interval-Poset : closed-interval-Poset → type-Poset X → UU l2
  is-in-closed-interval-Poset [x,y] =
    is-in-subtype (subposet-closed-interval-Poset [x,y])
```

## Properties

### Closed intervals are inhabited

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2) ([x,y] : closed-interval-Poset X)
  where

  abstract
    is-inhabited-closed-interval-Poset :
      is-inhabited-subtype (subposet-closed-interval-Poset X [x,y])
    is-inhabited-closed-interval-Poset =
      unit-trunc-Prop
        ( lower-bound-closed-interval-Poset X [x,y] ,
          refl-leq-Poset X _ ,
          pr2 (pr2 [x,y]))
```

### The map from closed intervals to subposets is injective

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  abstract
    is-injective-subposet-closed-interval-Poset :
      is-injective (subposet-closed-interval-Poset X)
    is-injective-subposet-closed-interval-Poset
      {a , b , a≤b} {c , d , c≤d} [a,b]=[c,d] =
        ap
          ( λ ((p , q) , r) → (p , q , r))
          ( eq-pair-Σ
            ( eq-pair
              ( antisymmetric-leq-Poset X a c
                ( pr1
                  ( backward-implication
                    ( has-same-elements-eq-subtype _ _ [a,b]=[c,d] c)
                    ( refl-leq-Poset X c , c≤d)))
                ( pr1
                  ( forward-implication
                    ( has-same-elements-eq-subtype _ _ [a,b]=[c,d] a)
                    ( refl-leq-Poset X a , a≤b))))
              ( antisymmetric-leq-Poset X b d
                ( pr2
                  ( forward-implication
                    ( has-same-elements-eq-subtype _ _ [a,b]=[c,d] b)
                    ( a≤b , refl-leq-Poset X b)))
                ( pr2
                  ( backward-implication
                    ( has-same-elements-eq-subtype _ _ [a,b]=[c,d] d)
                    ( c≤d , refl-leq-Poset X d)))))
            ( eq-type-Prop (leq-prop-Poset X _ _)))
```

### The property of a map of taking a closed interval to a closed interval

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Poset l1 l2) (Y : Poset l3 l4)
  (f : type-Poset X → type-Poset Y)
  where

  is-closed-interval-map-prop-Poset :
    ([a,b] : closed-interval-Poset X) →
    ([c,d] : closed-interval-Poset Y) →
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-closed-interval-map-prop-Poset [a,b] [c,d] =
    is-image-map-subtype-prop f
      ( subposet-closed-interval-Poset X [a,b])
      ( subposet-closed-interval-Poset Y [c,d])
```
