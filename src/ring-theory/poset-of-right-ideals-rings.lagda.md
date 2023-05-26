# The poset of right ideals in a ring

```agda
module ring-theory.poset-of-right-ideals-rings where
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

open import ring-theory.right-ideals-rings
open import ring-theory.rings
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

  leq-right-ideal-Ring-Prop :
    {l2 l3 : Level} →
    right-ideal-Ring l2 R → right-ideal-Ring l3 R → Prop (l1 ⊔ l2 ⊔ l3)
  leq-right-ideal-Ring-Prop I J =
    leq-subtype-Prop
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
    {l2 : Level} (I : right-ideal-Ring l2 R) → leq-right-ideal-Ring I I
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
    {l2 : Level} (I J : right-ideal-Ring l2 R) →
    leq-right-ideal-Ring I J → leq-right-ideal-Ring J I → I ＝ J
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
  leq-Large-Preorder-Prop right-ideal-Ring-Large-Preorder =
    leq-right-ideal-Ring-Prop R
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
