# Subgroups of higher groups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module higher-group-theory.subgroups-higher-groups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types funext univalence truncations
open import foundation.cartesian-product-types funext univalence
open import foundation.dependent-pair-types
open import foundation.function-types funext
open import foundation.sets funext univalence
open import foundation.universe-levels

open import higher-group-theory.higher-groups funext univalence truncations

open import structured-types.pointed-types
```

</details>

## Idea

A subgroup of a higher group is a pointed set bundle over its classifying type
with connected total space.

## Definition

```agda
subgroup-action-∞-Group :
  {l1 : Level} (l2 : Level) (G : ∞-Group l1) →
  classifying-type-∞-Group G → UU (l1 ⊔ lsuc l2)
subgroup-action-∞-Group l2 G u =
  Σ ( classifying-type-∞-Group G → Set l2)
    ( λ X →
      ( type-Set (X u)) ×
      ( is-0-connected (Σ (classifying-type-∞-Group G) (type-Set ∘ X))))

subgroup-∞-Group :
  {l1 : Level} (l2 : Level) (G : ∞-Group l1) → UU (l1 ⊔ lsuc l2)
subgroup-∞-Group l2 G = subgroup-action-∞-Group l2 G (shape-∞-Group G)

module _
  {l1 l2 : Level} (G : ∞-Group l1) (H : subgroup-∞-Group l2 G)
  where

  set-action-subgroup-∞-Group :
    classifying-type-∞-Group G → Set l2
  set-action-subgroup-∞-Group = pr1 H

  action-subgroup-∞-Group : classifying-type-∞-Group G → UU l2
  action-subgroup-∞-Group = type-Set ∘ set-action-subgroup-∞-Group

  classifying-type-subgroup-∞-Group : UU (l1 ⊔ l2)
  classifying-type-subgroup-∞-Group =
    Σ (classifying-type-∞-Group G) action-subgroup-∞-Group

  shape-subgroup-∞-Group : classifying-type-subgroup-∞-Group
  pr1 shape-subgroup-∞-Group = shape-∞-Group G
  pr2 shape-subgroup-∞-Group = pr1 (pr2 H)

  classifying-pointed-type-subgroup-∞-Group : Pointed-Type (l1 ⊔ l2)
  pr1 classifying-pointed-type-subgroup-∞-Group =
    classifying-type-subgroup-∞-Group
  pr2 classifying-pointed-type-subgroup-∞-Group =
    shape-subgroup-∞-Group

  is-connected-classifying-type-subgroup-∞-Group :
    is-0-connected classifying-type-subgroup-∞-Group
  is-connected-classifying-type-subgroup-∞-Group = pr2 (pr2 H)

  ∞-group-subgroup-∞-Group : ∞-Group (l1 ⊔ l2)
  pr1 ∞-group-subgroup-∞-Group = classifying-pointed-type-subgroup-∞-Group
  pr2 ∞-group-subgroup-∞-Group = is-connected-classifying-type-subgroup-∞-Group
```
