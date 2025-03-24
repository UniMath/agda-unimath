# The poset of right ideals of a ring

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module ring-theory.poset-of-right-ideals-rings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.identity-types funext
open import foundation.powersets funext univalence truncations
open import foundation.propositions funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels

open import order-theory.large-posets funext univalence truncations
open import order-theory.large-preorders funext univalence truncations
open import order-theory.order-preserving-maps-large-posets funext univalence truncations
open import order-theory.order-preserving-maps-large-preorders funext univalence truncations
open import order-theory.similarity-of-elements-large-posets funext univalence truncations

open import ring-theory.right-ideals-rings funext univalence truncations
open import ring-theory.rings funext univalence truncations
```

</details>

## Idea

The [right ideals](ring-theory.right-ideals-rings.md) of a
[ring](ring-theory.rings.md) form a [large poset](order-theory.large-posets.md)
ordered by inclusion.

## Definition

### The inclusion relation on right ideals

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  leq-prop-right-ideal-Ring :
    {l2 l3 : Level} →
    right-ideal-Ring l2 R → right-ideal-Ring l3 R → Prop (l1 ⊔ l2 ⊔ l3)
  leq-prop-right-ideal-Ring I J =
    leq-prop-subtype
      ( subset-right-ideal-Ring R I)
      ( subset-right-ideal-Ring R J)

  leq-right-ideal-Ring :
    {l2 l3 : Level} →
    right-ideal-Ring l2 R → right-ideal-Ring l3 R → UU (l1 ⊔ l2 ⊔ l3)
  leq-right-ideal-Ring I J =
    subset-right-ideal-Ring R I ⊆ subset-right-ideal-Ring R J

  is-prop-leq-right-ideal-Ring :
    {l2 l3 : Level} (I : right-ideal-Ring l2 R) (J : right-ideal-Ring l3 R) →
    is-prop (leq-right-ideal-Ring I J)
  is-prop-leq-right-ideal-Ring I J =
    is-prop-leq-subtype
      ( subset-right-ideal-Ring R I)
      ( subset-right-ideal-Ring R J)

  refl-leq-right-ideal-Ring :
    {l2 : Level} → is-reflexive (leq-right-ideal-Ring {l2})
  refl-leq-right-ideal-Ring I =
    refl-leq-subtype (subset-right-ideal-Ring R I)

  transitive-leq-right-ideal-Ring :
    {l2 l3 l4 : Level}
    (I : right-ideal-Ring l2 R)
    (J : right-ideal-Ring l3 R)
    (K : right-ideal-Ring l4 R) →
    leq-right-ideal-Ring J K →
    leq-right-ideal-Ring I J →
    leq-right-ideal-Ring I K
  transitive-leq-right-ideal-Ring I J K =
    transitive-leq-subtype
      ( subset-right-ideal-Ring R I)
      ( subset-right-ideal-Ring R J)
      ( subset-right-ideal-Ring R K)

  antisymmetric-leq-right-ideal-Ring :
    {l2 : Level} → is-antisymmetric (leq-right-ideal-Ring {l2})
  antisymmetric-leq-right-ideal-Ring I J U V =
    eq-has-same-elements-right-ideal-Ring R I J (λ x → U x , V x)
```

### The large poset of right ideals

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  right-ideal-Ring-Large-Preorder :
    Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  type-Large-Preorder right-ideal-Ring-Large-Preorder l =
    right-ideal-Ring l R
  leq-prop-Large-Preorder right-ideal-Ring-Large-Preorder =
    leq-prop-right-ideal-Ring R
  refl-leq-Large-Preorder right-ideal-Ring-Large-Preorder =
    refl-leq-right-ideal-Ring R
  transitive-leq-Large-Preorder right-ideal-Ring-Large-Preorder =
    transitive-leq-right-ideal-Ring R

  right-ideal-Ring-Large-Poset :
    Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  large-preorder-Large-Poset right-ideal-Ring-Large-Poset =
    right-ideal-Ring-Large-Preorder
  antisymmetric-leq-Large-Poset right-ideal-Ring-Large-Poset =
    antisymmetric-leq-right-ideal-Ring R
```

### The similarity relation on right ideals in a ring

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  sim-prop-right-ideal-Ring :
    {l2 l3 : Level} (I : right-ideal-Ring l2 R) (J : right-ideal-Ring l3 R) →
    Prop (l1 ⊔ l2 ⊔ l3)
  sim-prop-right-ideal-Ring =
    sim-prop-Large-Poset (right-ideal-Ring-Large-Poset R)

  sim-right-ideal-Ring :
    {l2 l3 : Level} (I : right-ideal-Ring l2 R) (J : right-ideal-Ring l3 R) →
    UU (l1 ⊔ l2 ⊔ l3)
  sim-right-ideal-Ring = sim-Large-Poset (right-ideal-Ring-Large-Poset R)

  is-prop-sim-right-ideal-Ring :
    {l2 l3 : Level} (I : right-ideal-Ring l2 R) (J : right-ideal-Ring l3 R) →
    is-prop (sim-right-ideal-Ring I J)
  is-prop-sim-right-ideal-Ring =
    is-prop-sim-Large-Poset (right-ideal-Ring-Large-Poset R)

  eq-sim-right-ideal-Ring :
    {l2 : Level} (I J : right-ideal-Ring l2 R) →
    sim-right-ideal-Ring I J → I ＝ J
  eq-sim-right-ideal-Ring = eq-sim-Large-Poset (right-ideal-Ring-Large-Poset R)
```

## Properties

### The forgetful function from right ideals to subsets preserves inclusions

```agda
module _
  {l : Level} (R : Ring l)
  where

  preserves-order-subset-right-ideal-Ring :
    {l1 l2 : Level} (I : right-ideal-Ring l1 R) (J : right-ideal-Ring l2 R) →
    leq-right-ideal-Ring R I J →
    subset-right-ideal-Ring R I ⊆ subset-right-ideal-Ring R J
  preserves-order-subset-right-ideal-Ring I J H = H

  subset-right-ideal-hom-large-poset-Ring :
    hom-Large-Poset
      ( λ l → l)
      ( right-ideal-Ring-Large-Poset R)
      ( powerset-Large-Poset (type-Ring R))
  map-hom-Large-Preorder subset-right-ideal-hom-large-poset-Ring =
    subset-right-ideal-Ring R
  preserves-order-hom-Large-Preorder subset-right-ideal-hom-large-poset-Ring =
    preserves-order-subset-right-ideal-Ring
```
