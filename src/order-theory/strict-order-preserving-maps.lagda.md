# Strict order preserving maps

```agda
module order-theory.strict-order-preserving-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.strictly-ordered-sets
open import order-theory.strictly-ordered-types
```

</details>

## Idea

Consider two [strictly ordered types](order-theory.strictly-ordered-types.md)
$P$ and $Q$, with orderings $<_P$ and $<_Q$ respectively. A
{{#concept "strict order preserving map" Agda=hom-Strictly-Ordered-Type}}
consists of map $f : P → Q$ between their underlying types such that for any two
elements $x<_P y$ in $P$ we have $f(x)<_Q f(y)$ in $Q$.

## Definitions

### The predicate on maps between strictly ordered types of preserving the strict ordering

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Strictly-Ordered-Type l1 l2) (Q : Strictly-Ordered-Type l3 l4)
  (f : type-Strictly-Ordered-Type P → type-Strictly-Ordered-Type Q)
  where

  preserves-strict-order-prop-map-Strictly-Ordered-Type :
    Prop (l1 ⊔ l2 ⊔ l4)
  preserves-strict-order-prop-map-Strictly-Ordered-Type =
    Π-Prop
      ( type-Strictly-Ordered-Type P)
      ( λ x →
        Π-Prop
          ( type-Strictly-Ordered-Type P)
          ( λ y →
            hom-Prop
              ( le-prop-Strictly-Ordered-Type P x y)
              ( le-prop-Strictly-Ordered-Type Q (f x) (f y))))

  preserves-strict-order-map-Strictly-Ordered-Type :
    UU (l1 ⊔ l2 ⊔ l4)
  preserves-strict-order-map-Strictly-Ordered-Type =
    type-Prop preserves-strict-order-prop-map-Strictly-Ordered-Type

  is-prop-preserves-strict-order-map-Strictly-Ordered-Type :
    is-prop preserves-strict-order-map-Strictly-Ordered-Type
  is-prop-preserves-strict-order-map-Strictly-Ordered-Type =
    is-prop-type-Prop preserves-strict-order-prop-map-Strictly-Ordered-Type
```

### The type of strict order preserving maps between strictly ordered types

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Strictly-Ordered-Type l1 l2) (Q : Strictly-Ordered-Type l3 l4)
  where

  hom-Strictly-Ordered-Type : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Strictly-Ordered-Type =
    type-subtype (preserves-strict-order-prop-map-Strictly-Ordered-Type P Q)

module _
  {l1 l2 l3 l4 : Level}
  (P : Strictly-Ordered-Type l1 l2) (Q : Strictly-Ordered-Type l3 l4)
  (f : hom-Strictly-Ordered-Type P Q)
  where

  map-hom-Strictly-Ordered-Type :
    type-Strictly-Ordered-Type P → type-Strictly-Ordered-Type Q
  map-hom-Strictly-Ordered-Type =
    pr1 f

  preserves-strict-order-hom-Strictly-Ordered-Type :
    preserves-strict-order-map-Strictly-Ordered-Type P Q
      ( map-hom-Strictly-Ordered-Type)
  preserves-strict-order-hom-Strictly-Ordered-Type =
    pr2 f
```

### The predicate on maps between strictly ordered sets of preserving the strict ordering

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Strictly-Ordered-Set l1 l2) (Q : Strictly-Ordered-Set l3 l4)
  (f : type-Strictly-Ordered-Set P → type-Strictly-Ordered-Set Q)
  where

  preserves-strict-order-prop-map-Strictly-Ordered-Set :
    Prop (l1 ⊔ l2 ⊔ l4)
  preserves-strict-order-prop-map-Strictly-Ordered-Set =
    preserves-strict-order-prop-map-Strictly-Ordered-Type
      ( strictly-ordered-type-Strictly-Ordered-Set P)
      ( strictly-ordered-type-Strictly-Ordered-Set Q)
      ( f)

  preserves-strict-order-map-Strictly-Ordered-Set :
    UU (l1 ⊔ l2 ⊔ l4)
  preserves-strict-order-map-Strictly-Ordered-Set =
    preserves-strict-order-map-Strictly-Ordered-Type
      ( strictly-ordered-type-Strictly-Ordered-Set P)
      ( strictly-ordered-type-Strictly-Ordered-Set Q)
      ( f)

  is-prop-preserves-strict-order-map-Strictly-Ordered-Set :
    is-prop preserves-strict-order-map-Strictly-Ordered-Set
  is-prop-preserves-strict-order-map-Strictly-Ordered-Set =
    is-prop-preserves-strict-order-map-Strictly-Ordered-Type
      ( strictly-ordered-type-Strictly-Ordered-Set P)
      ( strictly-ordered-type-Strictly-Ordered-Set Q)
      ( f)
```

### The type of strict order preserving maps between strictly ordered sets

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Strictly-Ordered-Set l1 l2) (Q : Strictly-Ordered-Set l3 l4)
  where

  hom-Strictly-Ordered-Set : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Strictly-Ordered-Set =
    type-subtype (preserves-strict-order-prop-map-Strictly-Ordered-Set P Q)

module _
  {l1 l2 l3 l4 : Level}
  (P : Strictly-Ordered-Set l1 l2) (Q : Strictly-Ordered-Set l3 l4)
  (f : hom-Strictly-Ordered-Set P Q)
  where

  map-hom-Strictly-Ordered-Set :
    type-Strictly-Ordered-Set P → type-Strictly-Ordered-Set Q
  map-hom-Strictly-Ordered-Set =
    pr1 f

  preserves-strict-order-hom-Strictly-Ordered-Set :
    preserves-strict-order-map-Strictly-Ordered-Set P Q
      ( map-hom-Strictly-Ordered-Set)
  preserves-strict-order-hom-Strictly-Ordered-Set =
    pr2 f
```
