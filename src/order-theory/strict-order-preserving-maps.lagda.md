# Strict order preserving maps

```agda
module order-theory.strict-order-preserving-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.strict-preorders
open import order-theory.strictly-preordered-sets
```

</details>

## Idea

Consider two [strict preorders](order-theory.strict-preorders.md) $P$ and $Q$,
with orderings $<_P$ and $<_Q$ respectively. A
{{#concept "strict order preserving map" Agda=hom-Strict-Preorder}} consists of
map $f : P → Q$ between their underlying types such that for any two elements
$x<_P y$ in $P$ we have $f(x)<_Q f(y)$ in $Q$.

## Definitions

### The predicate on maps between strict preorders of preserving the strict ordering

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Strict-Preorder l1 l2) (Q : Strict-Preorder l3 l4)
  (f : type-Strict-Preorder P → type-Strict-Preorder Q)
  where

  preserves-strict-order-prop-map-Strict-Preorder :
    Prop (l1 ⊔ l2 ⊔ l4)
  preserves-strict-order-prop-map-Strict-Preorder =
    Π-Prop
      ( type-Strict-Preorder P)
      ( λ x →
        Π-Prop
          ( type-Strict-Preorder P)
          ( λ y →
            hom-Prop
              ( le-prop-Strict-Preorder P x y)
              ( le-prop-Strict-Preorder Q (f x) (f y))))

  preserves-strict-order-map-Strict-Preorder :
    UU (l1 ⊔ l2 ⊔ l4)
  preserves-strict-order-map-Strict-Preorder =
    type-Prop preserves-strict-order-prop-map-Strict-Preorder

  is-prop-preserves-strict-order-map-Strict-Preorder :
    is-prop preserves-strict-order-map-Strict-Preorder
  is-prop-preserves-strict-order-map-Strict-Preorder =
    is-prop-type-Prop preserves-strict-order-prop-map-Strict-Preorder
```

### The type of strict order preserving maps between strict preorders

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Strict-Preorder l1 l2) (Q : Strict-Preorder l3 l4)
  where

  hom-Strict-Preorder : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Strict-Preorder =
    type-subtype (preserves-strict-order-prop-map-Strict-Preorder P Q)

module _
  {l1 l2 l3 l4 : Level}
  (P : Strict-Preorder l1 l2) (Q : Strict-Preorder l3 l4)
  (f : hom-Strict-Preorder P Q)
  where

  map-hom-Strict-Preorder :
    type-Strict-Preorder P → type-Strict-Preorder Q
  map-hom-Strict-Preorder =
    pr1 f

  preserves-strict-order-hom-Strict-Preorder :
    preserves-strict-order-map-Strict-Preorder P Q
      ( map-hom-Strict-Preorder)
  preserves-strict-order-hom-Strict-Preorder =
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
    preserves-strict-order-prop-map-Strict-Preorder
      ( strict-preorder-Strictly-Preordered-Set P)
      ( strict-preorder-Strictly-Preordered-Set Q)
      ( f)

  preserves-strict-order-map-Strictly-Preordered-Set :
    UU (l1 ⊔ l2 ⊔ l4)
  preserves-strict-order-map-Strictly-Preordered-Set =
    preserves-strict-order-map-Strict-Preorder
      ( strict-preorder-Strictly-Preordered-Set P)
      ( strict-preorder-Strictly-Preordered-Set Q)
      ( f)

  is-prop-preserves-strict-order-map-Strictly-Preordered-Set :
    is-prop preserves-strict-order-map-Strictly-Preordered-Set
  is-prop-preserves-strict-order-map-Strictly-Preordered-Set =
    is-prop-preserves-strict-order-map-Strict-Preorder
      ( strict-preorder-Strictly-Preordered-Set P)
      ( strict-preorder-Strictly-Preordered-Set Q)
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

## Properties

### The identity homomorphism of strictly preordered sets

```agda
module _
  {l1 l2 : Level} (P : Strictly-Preordered-Set l1 l2)
  where

  id-hom-Strictly-Preordered-Set : hom-Strictly-Preordered-Set P P
  id-hom-Strictly-Preordered-Set = (λ x → x) , (λ x y H → H)
```

### The composition of strict order preserving maps preserves the strict ordering

```agda
module _
  {l1 l1' l2 l2' l3 l3' : Level}
  (P : Strict-Preorder l1 l1')
  (Q : Strict-Preorder l2 l2')
  (R : Strict-Preorder l3 l3')
  (g : type-Strict-Preorder Q → type-Strict-Preorder R)
  (f : type-Strict-Preorder P → type-Strict-Preorder Q)
  where

  preserves-strict-order-comp-preserves-strict-order-map-Strict-Preorder :
    preserves-strict-order-map-Strict-Preorder Q R g →
    preserves-strict-order-map-Strict-Preorder P Q f →
    preserves-strict-order-map-Strict-Preorder P R (g ∘ f)
  preserves-strict-order-comp-preserves-strict-order-map-Strict-Preorder
    G F x y = G (f x) (f y) ∘ (F x y)
```

### Strict order preserving composition of strict order preserving maps between strict preorders

```agda
module _
  {l1 l1' l2 l2' l3 l3' : Level}
  (P : Strict-Preorder l1 l1')
  (Q : Strict-Preorder l2 l2')
  (R : Strict-Preorder l3 l3')
  (g : hom-Strict-Preorder Q R)
  (f : hom-Strict-Preorder P Q)
  where

  comp-hom-Strict-Preorder : hom-Strict-Preorder P R
  comp-hom-Strict-Preorder =
    map-hom-Strict-Preorder Q R g ∘ map-hom-Strict-Preorder P Q f ,
    preserves-strict-order-comp-preserves-strict-order-map-Strict-Preorder P Q R
      ( map-hom-Strict-Preorder Q R g)
      ( map-hom-Strict-Preorder P Q f)
      ( preserves-strict-order-hom-Strict-Preorder Q R g)
      ( preserves-strict-order-hom-Strict-Preorder P Q f)
```

### Strict order preserving composition of strict order preserving maps between strictly preordered sets

```agda
module _
  {l1 l1' l2 l2' l3 l3' : Level}
  (P : Strictly-Preordered-Set l1 l1')
  (Q : Strictly-Preordered-Set l2 l2')
  (R : Strictly-Preordered-Set l3 l3')
  (g : hom-Strictly-Preordered-Set Q R)
  (f : hom-Strictly-Preordered-Set P Q)
  where

  comp-hom-Strictly-Preordered-Set : hom-Strictly-Preordered-Set P R
  comp-hom-Strictly-Preordered-Set =
    comp-hom-Strict-Preorder
      ( strict-preorder-Strictly-Preordered-Set P)
      ( strict-preorder-Strictly-Preordered-Set Q)
      ( strict-preorder-Strictly-Preordered-Set R)
      ( g)
      ( f)
```
