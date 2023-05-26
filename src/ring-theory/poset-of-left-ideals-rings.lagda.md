# The poset of left ideals in a ring

```agda
module ring-theory.poset-of-left-ideals-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-preorders

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

  leq-left-ideal-Ring-Prop :
    {l2 l3 : Level} →
    left-ideal-Ring l2 R → left-ideal-Ring l3 R → Prop (l1 ⊔ l2 ⊔ l3)
  leq-left-ideal-Ring-Prop I J =
    leq-subtype-Prop
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
    {l2 : Level} (I : left-ideal-Ring l2 R) → leq-left-ideal-Ring I I
  refl-leq-left-ideal-Ring I =
    refl-leq-subtype (subset-left-ideal-Ring R I)

  transitive-leq-left-ideal-Ring :
    {l2 l3 l4 : Level}
    (I : left-ideal-Ring l2 R)
    (J : left-ideal-Ring l3 R)
    (K : left-ideal-Ring l4 R) →
    leq-left-ideal-Ring J K → leq-left-ideal-Ring I J → leq-left-ideal-Ring I K
  transitive-leq-left-ideal-Ring I J K =
    transitive-leq-subtype
      ( subset-left-ideal-Ring R I)
      ( subset-left-ideal-Ring R J)
      ( subset-left-ideal-Ring R K)

  antisymmetric-leq-left-ideal-Ring :
    {l2 : Level} (I J : left-ideal-Ring l2 R) →
    leq-left-ideal-Ring I J → leq-left-ideal-Ring J I → I ＝ J
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
  leq-Large-Preorder-Prop left-ideal-Ring-Large-Preorder =
    leq-left-ideal-Ring-Prop R
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
