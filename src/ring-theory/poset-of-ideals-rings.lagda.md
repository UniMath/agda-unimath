# The poset of ideals of a ring

```agda
module ring-theory.poset-of-ideals-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
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

open import ring-theory.ideals-rings
open import ring-theory.rings
```

</details>

## Idea

The [ideals](ring-theory.ideals-rings.md) of a [ring](ring-theory.rings.md) form
a [large poset](order-theory.large-posets.md) ordered by inclusion.

## Definition

### The inclusion relation on ideals

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  leq-prop-ideal-Ring :
    {l2 l3 : Level} → ideal-Ring l2 R → ideal-Ring l3 R → Prop (l1 ⊔ l2 ⊔ l3)
  leq-prop-ideal-Ring I J =
    leq-prop-subtype
      ( subset-ideal-Ring R I)
      ( subset-ideal-Ring R J)

  leq-ideal-Ring :
    {l2 l3 : Level} → ideal-Ring l2 R → ideal-Ring l3 R → UU (l1 ⊔ l2 ⊔ l3)
  leq-ideal-Ring I J =
    subset-ideal-Ring R I ⊆ subset-ideal-Ring R J

  is-prop-leq-ideal-Ring :
    {l2 l3 : Level} (I : ideal-Ring l2 R) (J : ideal-Ring l3 R) →
    is-prop (leq-ideal-Ring I J)
  is-prop-leq-ideal-Ring I J =
    is-prop-leq-subtype (subset-ideal-Ring R I) (subset-ideal-Ring R J)

  refl-leq-ideal-Ring :
    {l2 : Level} → is-reflexive (leq-ideal-Ring {l2})
  refl-leq-ideal-Ring I =
    refl-leq-subtype (subset-ideal-Ring R I)

  transitive-leq-ideal-Ring :
    {l2 l3 l4 : Level}
    (I : ideal-Ring l2 R)
    (J : ideal-Ring l3 R)
    (K : ideal-Ring l4 R) →
    leq-ideal-Ring J K →
    leq-ideal-Ring I J →
    leq-ideal-Ring I K
  transitive-leq-ideal-Ring I J K =
    transitive-leq-subtype
      ( subset-ideal-Ring R I)
      ( subset-ideal-Ring R J)
      ( subset-ideal-Ring R K)

  antisymmetric-leq-ideal-Ring :
    {l2 : Level} → is-antisymmetric (leq-ideal-Ring {l2})
  antisymmetric-leq-ideal-Ring I J U V =
    eq-has-same-elements-ideal-Ring R I J (λ x → U x , V x)
```

### The large poset of ideals

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  ideal-Ring-Large-Preorder :
    Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  type-Large-Preorder ideal-Ring-Large-Preorder l = ideal-Ring l R
  leq-prop-Large-Preorder ideal-Ring-Large-Preorder = leq-prop-ideal-Ring R
  refl-leq-Large-Preorder ideal-Ring-Large-Preorder = refl-leq-ideal-Ring R
  transitive-leq-Large-Preorder ideal-Ring-Large-Preorder =
    transitive-leq-ideal-Ring R

  ideal-Ring-Large-Poset :
    Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  large-preorder-Large-Poset ideal-Ring-Large-Poset = ideal-Ring-Large-Preorder
  antisymmetric-leq-Large-Poset ideal-Ring-Large-Poset =
    antisymmetric-leq-ideal-Ring R
```

### The similarity relation on ideals in a ring

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  sim-prop-ideal-Ring :
    {l2 l3 : Level} (I : ideal-Ring l2 R) (J : ideal-Ring l3 R) →
    Prop (l1 ⊔ l2 ⊔ l3)
  sim-prop-ideal-Ring =
    sim-prop-Large-Poset (ideal-Ring-Large-Poset R)

  sim-ideal-Ring :
    {l2 l3 : Level} (I : ideal-Ring l2 R) (J : ideal-Ring l3 R) →
    UU (l1 ⊔ l2 ⊔ l3)
  sim-ideal-Ring = sim-Large-Poset (ideal-Ring-Large-Poset R)

  is-prop-sim-ideal-Ring :
    {l2 l3 : Level} (I : ideal-Ring l2 R) (J : ideal-Ring l3 R) →
    is-prop (sim-ideal-Ring I J)
  is-prop-sim-ideal-Ring =
    is-prop-sim-Large-Poset (ideal-Ring-Large-Poset R)

  eq-sim-ideal-Ring :
    {l2 : Level} (I J : ideal-Ring l2 R) → sim-ideal-Ring I J → I ＝ J
  eq-sim-ideal-Ring = eq-sim-Large-Poset (ideal-Ring-Large-Poset R)
```

## Properties

### The forgetful function from ideals to subsets preserves inclusions

```agda
module _
  {l : Level} (R : Ring l)
  where

  preserves-order-subset-ideal-Ring :
    {l1 l2 : Level} (I : ideal-Ring l1 R) (J : ideal-Ring l2 R) →
    leq-ideal-Ring R I J → subset-ideal-Ring R I ⊆ subset-ideal-Ring R J
  preserves-order-subset-ideal-Ring I J H = H

  subset-ideal-hom-large-poset-Ring :
    hom-Large-Poset
      ( λ l → l)
      ( ideal-Ring-Large-Poset R)
      ( powerset-Large-Poset (type-Ring R))
  map-hom-Large-Preorder subset-ideal-hom-large-poset-Ring =
    subset-ideal-Ring R
  preserves-order-hom-Large-Preorder subset-ideal-hom-large-poset-Ring =
    preserves-order-subset-ideal-Ring
```
