# The poset of left ideals of a ring

```agda
module ring-theory.poset-of-left-ideals-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.powersets
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.similarity-of-elements-large-posets

open import ring-theory.left-ideals-rings
open import ring-theory.rings
```

</details>

## Idea

The [left ideals](ring-theory.left-ideals-rings.md) of a
[ring](ring-theory.rings.md) form a [large poset](order-theory.large-posets.md)
ordered by inclusion.

## Definition

### The inclusion relation on left ideals

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  leq-prop-left-ideal-Ring :
    {l2 l3 : Level} →
    left-ideal-Ring l2 R → left-ideal-Ring l3 R → Prop (l1 ⊔ l2 ⊔ l3)
  leq-prop-left-ideal-Ring I J =
    leq-prop-subtype
      ( subset-left-ideal-Ring R I)
      ( subset-left-ideal-Ring R J)

  leq-left-ideal-Ring :
    {l2 l3 : Level} →
    left-ideal-Ring l2 R → left-ideal-Ring l3 R → UU (l1 ⊔ l2 ⊔ l3)
  leq-left-ideal-Ring I J =
    subset-left-ideal-Ring R I ⊆ subset-left-ideal-Ring R J

  is-prop-leq-left-ideal-Ring :
    {l2 l3 : Level} (I : left-ideal-Ring l2 R) (J : left-ideal-Ring l3 R) →
    is-prop (leq-left-ideal-Ring I J)
  is-prop-leq-left-ideal-Ring I J =
    is-prop-leq-subtype
      ( subset-left-ideal-Ring R I)
      ( subset-left-ideal-Ring R J)

  refl-leq-left-ideal-Ring :
    {l2 : Level} → is-reflexive (leq-left-ideal-Ring {l2})
  refl-leq-left-ideal-Ring I =
    refl-leq-subtype (subset-left-ideal-Ring R I)

  transitive-leq-left-ideal-Ring :
    {l2 l3 l4 : Level}
    (I : left-ideal-Ring l2 R)
    (J : left-ideal-Ring l3 R)
    (K : left-ideal-Ring l4 R) →
    leq-left-ideal-Ring J K →
    leq-left-ideal-Ring I J →
    leq-left-ideal-Ring I K
  transitive-leq-left-ideal-Ring I J K =
    transitive-leq-subtype
      ( subset-left-ideal-Ring R I)
      ( subset-left-ideal-Ring R J)
      ( subset-left-ideal-Ring R K)

  antisymmetric-leq-left-ideal-Ring :
    {l2 : Level} → is-antisymmetric (leq-left-ideal-Ring {l2})
  antisymmetric-leq-left-ideal-Ring I J U V =
    eq-has-same-elements-left-ideal-Ring R I J (λ x → U x , V x)
```

### The large poset of left ideals

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  left-ideal-Ring-Large-Preorder :
    Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  type-Large-Preorder left-ideal-Ring-Large-Preorder l =
    left-ideal-Ring l R
  leq-prop-Large-Preorder left-ideal-Ring-Large-Preorder =
    leq-prop-left-ideal-Ring R
  refl-leq-Large-Preorder left-ideal-Ring-Large-Preorder =
    refl-leq-left-ideal-Ring R
  transitive-leq-Large-Preorder left-ideal-Ring-Large-Preorder =
    transitive-leq-left-ideal-Ring R

  left-ideal-Ring-Large-Poset :
    Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  large-preorder-Large-Poset left-ideal-Ring-Large-Poset =
    left-ideal-Ring-Large-Preorder
  antisymmetric-leq-Large-Poset left-ideal-Ring-Large-Poset =
    antisymmetric-leq-left-ideal-Ring R
```

### The similarity relation on left ideals in a ring

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  sim-prop-left-ideal-Ring :
    {l2 l3 : Level} (I : left-ideal-Ring l2 R) (J : left-ideal-Ring l3 R) →
    Prop (l1 ⊔ l2 ⊔ l3)
  sim-prop-left-ideal-Ring =
    sim-prop-Large-Poset (left-ideal-Ring-Large-Poset R)

  sim-left-ideal-Ring :
    {l2 l3 : Level} (I : left-ideal-Ring l2 R) (J : left-ideal-Ring l3 R) →
    UU (l1 ⊔ l2 ⊔ l3)
  sim-left-ideal-Ring = sim-Large-Poset (left-ideal-Ring-Large-Poset R)

  is-prop-sim-left-ideal-Ring :
    {l2 l3 : Level} (I : left-ideal-Ring l2 R) (J : left-ideal-Ring l3 R) →
    is-prop (sim-left-ideal-Ring I J)
  is-prop-sim-left-ideal-Ring =
    is-prop-sim-Large-Poset (left-ideal-Ring-Large-Poset R)

  eq-sim-left-ideal-Ring :
    {l2 : Level} (I J : left-ideal-Ring l2 R) → sim-left-ideal-Ring I J → I ＝ J
  eq-sim-left-ideal-Ring = eq-sim-Large-Poset (left-ideal-Ring-Large-Poset R)
```

## Properties

### The forgetful function from left ideals to subsets preserves inclusions

```agda
module _
  {l : Level} (R : Ring l)
  where

  preserves-order-subset-left-ideal-Ring :
    {l1 l2 : Level} (I : left-ideal-Ring l1 R) (J : left-ideal-Ring l2 R) →
    leq-left-ideal-Ring R I J →
    subset-left-ideal-Ring R I ⊆ subset-left-ideal-Ring R J
  preserves-order-subset-left-ideal-Ring I J H = H

  subset-left-ideal-hom-large-poset-Ring :
    hom-set-Large-Poset
      ( id)
      ( left-ideal-Ring-Large-Poset R)
      ( powerset-Large-Poset (type-Ring R))
  map-hom-Large-Preorder subset-left-ideal-hom-large-poset-Ring =
    subset-left-ideal-Ring R
  preserves-order-hom-Large-Preorder subset-left-ideal-hom-large-poset-Ring =
    preserves-order-subset-left-ideal-Ring
```
