# Kernels of homomorphisms of concrete groups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.kernels-homomorphisms-concrete-groups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types funext univalence truncations
open import foundation.1-types funext univalence
open import foundation.connected-components funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps funext
open import foundation.sets funext univalence
open import foundation.truncated-maps funext
open import foundation.truncation-levels
open import foundation.universe-levels

open import group-theory.concrete-groups funext univalence truncations
open import group-theory.homomorphisms-concrete-groups funext univalence truncations

open import higher-group-theory.higher-groups funext univalence truncations

open import structured-types.pointed-types
```

</details>

## Idea

The kernel of a concrete group homomorphsim `Bf : BG →∗ BH` is the connected
component at the base point of the fiber of `Bf`.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : Concrete-Group l2)
  (f : hom-Concrete-Group G H)
  where

  classifying-type-kernel-hom-Concrete-Group : UU (l1 ⊔ l2)
  classifying-type-kernel-hom-Concrete-Group =
    connected-component
      ( fiber
        ( classifying-map-hom-Concrete-Group G H f)
        ( shape-Concrete-Group H))
      ( pair
        ( shape-Concrete-Group G)
        ( preserves-point-classifying-map-hom-Concrete-Group G H f))

  shape-kernel-hom-Concrete-Group :
    classifying-type-kernel-hom-Concrete-Group
  shape-kernel-hom-Concrete-Group =
    point-connected-component
      ( fiber
        ( classifying-map-hom-Concrete-Group G H f)
        ( shape-Concrete-Group H))
      ( shape-Concrete-Group G
        , preserves-point-classifying-map-hom-Concrete-Group G H f)

  classifying-pointed-type-kernel-hom-Concrete-Group : Pointed-Type (l1 ⊔ l2)
  pr1 classifying-pointed-type-kernel-hom-Concrete-Group =
    classifying-type-kernel-hom-Concrete-Group
  pr2 classifying-pointed-type-kernel-hom-Concrete-Group =
    shape-kernel-hom-Concrete-Group

  is-0-connected-classifying-type-kernel-hom-Concrete-Group :
    is-0-connected classifying-type-kernel-hom-Concrete-Group
  is-0-connected-classifying-type-kernel-hom-Concrete-Group =
    is-0-connected-connected-component _ _

  is-1-type-classifying-type-kernel-hom-Concrete-Group :
    is-1-type classifying-type-kernel-hom-Concrete-Group
  is-1-type-classifying-type-kernel-hom-Concrete-Group =
    is-trunc-connected-component _ _
      ( is-trunc-map-is-trunc-domain-codomain
        ( one-𝕋)
        ( is-1-type-classifying-type-Concrete-Group G)
        ( is-1-type-classifying-type-Concrete-Group H)
        ( shape-Concrete-Group H))

  ∞-group-kernel-hom-Concrete-Group : ∞-Group (l1 ⊔ l2)
  pr1 ∞-group-kernel-hom-Concrete-Group =
    classifying-pointed-type-kernel-hom-Concrete-Group
  pr2 ∞-group-kernel-hom-Concrete-Group =
    is-0-connected-classifying-type-kernel-hom-Concrete-Group

  type-kernel-hom-Concrete-Group : UU (l1 ⊔ l2)
  type-kernel-hom-Concrete-Group =
    type-∞-Group ∞-group-kernel-hom-Concrete-Group

  is-set-type-kernel-hom-Concrete-Group :
    is-set type-kernel-hom-Concrete-Group
  is-set-type-kernel-hom-Concrete-Group =
    is-1-type-classifying-type-kernel-hom-Concrete-Group
      shape-kernel-hom-Concrete-Group
      shape-kernel-hom-Concrete-Group

  concrete-group-kernel-hom-Concrete-Group : Concrete-Group (l1 ⊔ l2)
  pr1 concrete-group-kernel-hom-Concrete-Group =
    ∞-group-kernel-hom-Concrete-Group
  pr2 concrete-group-kernel-hom-Concrete-Group =
    is-set-type-kernel-hom-Concrete-Group
```
