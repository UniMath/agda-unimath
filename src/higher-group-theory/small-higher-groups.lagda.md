# Small ∞-groups

```agda
module higher-group-theory.small-higher-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.images
open import foundation.locally-small-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.replacement
open import foundation.small-types
open import foundation.unit-type
open import foundation.universe-levels

open import higher-group-theory.higher-groups
```

</details>

## Idea

An [∞-group](higher-group-theory.higher-groups.md) `G` is said to be {{#concept "small" Disambiguation="∞-group" Agda=is-small-∞-Group}} with respect to a universe `𝒰` if its underlying type is `𝒰`-small. By the [type theoretic replacement principle](foundation.replacement.md) it follows that `G` is small if and only if its classifying type `BG` is small.

## Definitions

### The predicate of being a small ∞-group

```agda
module _
  {l1 : Level} (l2 : Level) (G : ∞-Group l1)
  where
  
  is-small-prop-∞-Group : Prop (l1 ⊔ lsuc l2)
  is-small-prop-∞-Group = is-small-Prop l2 (type-∞-Group G)

  is-small-∞-Group : UU (l1 ⊔ lsuc l2)
  is-small-∞-Group = is-small l2 (type-∞-Group G)

  is-prop-is-small-∞-Group : is-prop is-small-∞-Group
  is-prop-is-small-∞-Group = is-prop-is-small l2 (type-∞-Group G)
```

## Properties

### The classifying type of any small ∞-group is locally small

```agda
module _
  {l1 l2 : Level} (G : ∞-Group l1) (H : is-small-∞-Group l2 G)
  where

  is-locally-small-classifying-type-is-small-∞-Group' :
    (x y : classifying-type-∞-Group G) →
    shape-∞-Group G ＝ x → shape-∞-Group G ＝ y →
    is-small l2 (x ＝ y)
  is-locally-small-classifying-type-is-small-∞-Group' ._ ._ refl refl = H

  is-locally-small-classifying-type-is-small-∞-Group :
    is-locally-small l2 (classifying-type-∞-Group G)
  is-locally-small-classifying-type-is-small-∞-Group x y =
    apply-twice-universal-property-trunc-Prop
      ( mere-eq-classifying-type-∞-Group G (shape-∞-Group G) x)
      ( mere-eq-classifying-type-∞-Group G (shape-∞-Group G) y)
      ( is-small-Prop l2 (x ＝ y))
      ( is-locally-small-classifying-type-is-small-∞-Group' x y)
```

### An ∞-group is small if and only if its classifying type is small

```agda
module _
  {l1 l2 : Level} (G : ∞-Group l1)
  where

  is-small-classifying-type-is-small-∞-Group :
    is-small-∞-Group l2 G → is-small l2 (classifying-type-∞-Group G)
  is-small-classifying-type-is-small-∞-Group H =
    is-small-equiv'
      ( im (point-∞-Group G))
      ( compute-im-point-∞-Group G)
      ( replacement
        ( point-∞-Group G)
        ( is-small-unit)
        ( is-locally-small-classifying-type-is-small-∞-Group G H))

  is-small-is-small-classifying-type-∞-Group :
    is-small l2 (classifying-type-∞-Group G) → is-small-∞-Group l2 G
  is-small-is-small-classifying-type-∞-Group H =
    is-locally-small-is-small H (shape-∞-Group G) (shape-∞-Group G)
```
