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

open import order-theory.strictly-preordered-sets
open import order-theory.strictly-preordered-types
```

</details>

## Idea

Consider two
[strictly preordered types](order-theory.strictly-preordered-types.md) $P$ and
$Q$, with orderings $<_P$ and $<_Q$ respectively. A
{{#concept "strict order preserving map" Agda=hom-Strictly-Preordered-Type}}
consists of map $f : P → Q$ between their underlying types such that for any two
elements $x<_P y$ in $P$ we have $f(x)<_Q f(y)$ in $Q$.

## Definitions

### The predicate on maps between strictly preordered types of preserving the strict ordering

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Strictly-Preordered-Type l1 l2) (Q : Strictly-Preordered-Type l3 l4)
  (f : type-Strictly-Preordered-Type P → type-Strictly-Preordered-Type Q)
  where

  preserves-strict-order-prop-map-Strictly-Preordered-Type :
    Prop (l1 ⊔ l2 ⊔ l4)
  preserves-strict-order-prop-map-Strictly-Preordered-Type =
    Π-Prop
      ( type-Strictly-Preordered-Type P)
      ( λ x →
        Π-Prop
          ( type-Strictly-Preordered-Type P)
          ( λ y →
            hom-Prop
              ( le-prop-Strictly-Preordered-Type P x y)
              ( le-prop-Strictly-Preordered-Type Q (f x) (f y))))

  preserves-strict-order-map-Strictly-Preordered-Type :
    UU (l1 ⊔ l2 ⊔ l4)
  preserves-strict-order-map-Strictly-Preordered-Type =
    type-Prop preserves-strict-order-prop-map-Strictly-Preordered-Type

  is-prop-preserves-strict-order-map-Strictly-Preordered-Type :
    is-prop preserves-strict-order-map-Strictly-Preordered-Type
  is-prop-preserves-strict-order-map-Strictly-Preordered-Type =
    is-prop-type-Prop preserves-strict-order-prop-map-Strictly-Preordered-Type
```

### The type of strict order preserving maps between strictly preordered types

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Strictly-Preordered-Type l1 l2) (Q : Strictly-Preordered-Type l3 l4)
  where

  hom-Strictly-Preordered-Type : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Strictly-Preordered-Type =
    type-subtype (preserves-strict-order-prop-map-Strictly-Preordered-Type P Q)

module _
  {l1 l2 l3 l4 : Level}
  (P : Strictly-Preordered-Type l1 l2) (Q : Strictly-Preordered-Type l3 l4)
  (f : hom-Strictly-Preordered-Type P Q)
  where

  map-hom-Strictly-Preordered-Type :
    type-Strictly-Preordered-Type P → type-Strictly-Preordered-Type Q
  map-hom-Strictly-Preordered-Type =
    pr1 f

  preserves-strict-order-hom-Strictly-Preordered-Type :
    preserves-strict-order-map-Strictly-Preordered-Type P Q
      ( map-hom-Strictly-Preordered-Type)
  preserves-strict-order-hom-Strictly-Preordered-Type =
    pr2 f
```

### The predicate on maps between strictly preordered sets of preserving the strict ordering

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Strictly-Preordered-Set l1 l2) (Q : Strictly-Preordered-Set l3 l4)
  (f : type-Strictly-Preordered-Set P → type-Strictly-Preordered-Set Q)
  where

  preserves-strict-order-prop-map-Strictly-Preordered-Set :
    Prop (l1 ⊔ l2 ⊔ l4)
  preserves-strict-order-prop-map-Strictly-Preordered-Set =
    preserves-strict-order-prop-map-Strictly-Preordered-Type
      ( strictly-preordered-type-Strictly-Preordered-Set P)
      ( strictly-preordered-type-Strictly-Preordered-Set Q)
      ( f)

  preserves-strict-order-map-Strictly-Preordered-Set :
    UU (l1 ⊔ l2 ⊔ l4)
  preserves-strict-order-map-Strictly-Preordered-Set =
    preserves-strict-order-map-Strictly-Preordered-Type
      ( strictly-preordered-type-Strictly-Preordered-Set P)
      ( strictly-preordered-type-Strictly-Preordered-Set Q)
      ( f)

  is-prop-preserves-strict-order-map-Strictly-Preordered-Set :
    is-prop preserves-strict-order-map-Strictly-Preordered-Set
  is-prop-preserves-strict-order-map-Strictly-Preordered-Set =
    is-prop-preserves-strict-order-map-Strictly-Preordered-Type
      ( strictly-preordered-type-Strictly-Preordered-Set P)
      ( strictly-preordered-type-Strictly-Preordered-Set Q)
      ( f)
```

### The type of strict order preserving maps between strictly preordered sets

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Strictly-Preordered-Set l1 l2) (Q : Strictly-Preordered-Set l3 l4)
  where

  hom-Strictly-Preordered-Set : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Strictly-Preordered-Set =
    type-subtype (preserves-strict-order-prop-map-Strictly-Preordered-Set P Q)

module _
  {l1 l2 l3 l4 : Level}
  (P : Strictly-Preordered-Set l1 l2) (Q : Strictly-Preordered-Set l3 l4)
  (f : hom-Strictly-Preordered-Set P Q)
  where

  map-hom-Strictly-Preordered-Set :
    type-Strictly-Preordered-Set P → type-Strictly-Preordered-Set Q
  map-hom-Strictly-Preordered-Set =
    pr1 f

  preserves-strict-order-hom-Strictly-Preordered-Set :
    preserves-strict-order-map-Strictly-Preordered-Set P Q
      ( map-hom-Strictly-Preordered-Set)
  preserves-strict-order-hom-Strictly-Preordered-Set =
    pr2 f
```
