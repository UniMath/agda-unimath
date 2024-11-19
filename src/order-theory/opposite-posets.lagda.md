# Opposite posets

```agda
module order-theory.opposite-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.opposite-preorders
open import order-theory.order-preserving-maps-posets
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

Let `X` be a [poset](order-theory.posets.md), its
{{#concept "opposite" Disambiguation="poset" Agda=opposite-Poset}} `Xᵒᵖ` is
given by reversing the relation.

## Definition

### The opposite poset

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  preorder-opposite-Poset : Preorder l1 l2
  preorder-opposite-Poset =
    opposite-Preorder (preorder-Poset P)

  type-opposite-Poset : UU l1
  type-opposite-Poset = type-Preorder preorder-opposite-Poset

  leq-prop-opposite-Poset : (X Y : type-opposite-Poset) → Prop l2
  leq-prop-opposite-Poset =
    leq-prop-Preorder preorder-opposite-Poset

  leq-opposite-Poset : (X Y : type-opposite-Poset) → UU l2
  leq-opposite-Poset =
    leq-Preorder preorder-opposite-Poset

  transitive-leq-opposite-Poset :
    (X Y Z : type-opposite-Poset) →
    leq-opposite-Poset Y Z →
    leq-opposite-Poset X Y →
    leq-opposite-Poset X Z
  transitive-leq-opposite-Poset =
    transitive-leq-Preorder preorder-opposite-Poset

  refl-leq-opposite-Poset :
    (X : type-opposite-Poset) → leq-opposite-Poset X X
  refl-leq-opposite-Poset =
    refl-leq-Preorder preorder-opposite-Poset

  antisymmetric-leq-opposite-Poset :
    (X Y : type-opposite-Poset) →
    leq-opposite-Poset X Y →
    leq-opposite-Poset Y X →
    X ＝ Y
  antisymmetric-leq-opposite-Poset X Y p q =
    antisymmetric-leq-Poset P X Y q p

  opposite-Poset : Poset l1 l2
  opposite-Poset =
    ( preorder-opposite-Poset , antisymmetric-leq-opposite-Poset)
```

### The opposite functorial action on order preserving maps of posets

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  opposite-hom-Poset :
    hom-Poset P Q → hom-Poset (opposite-Poset P) (opposite-Poset Q)
  opposite-hom-Poset =
    opposite-hom-Preorder (preorder-Poset P) (preorder-Poset Q)
```

## Properties

### The opposite poset construction is a strict involution

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-involution-opposite-Poset : opposite-Poset (opposite-Poset P) ＝ P
  is-involution-opposite-Poset = refl

module _
  {l1 l2 l3 l4 : Level}
  (P : Poset l1 l2) (Q : Poset l3 l4)
  (f : hom-Poset P Q)
  where

  is-involution-opposite-hom-Poset :
    opposite-hom-Poset
      ( opposite-Poset P)
      ( opposite-Poset Q)
      ( opposite-hom-Poset P Q f) ＝
    f
  is-involution-opposite-hom-Poset = refl
```
