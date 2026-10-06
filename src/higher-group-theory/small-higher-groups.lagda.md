# Small ∞-groups

```agda
module higher-group-theory.small-higher-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.equivalences
open import foundation.identity-types
open import foundation.images
open import foundation.locally-small-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.replacement
open import foundation.small-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import higher-group-theory.equivalences-higher-groups
open import higher-group-theory.higher-groups

open import structured-types.pointed-equivalences
open import structured-types.pointed-types
open import structured-types.small-pointed-types
```

</details>

## Idea

An [∞-group](higher-group-theory.higher-groups.md) `G` is said to be
{{#concept "small" Disambiguation="∞-group" Agda=is-small-∞-Group}} with respect
to a universe `𝒰` if its underlying type is `𝒰`-small. By the
[type theoretic replacement principle](foundation.replacement.md) it follows
that `G` is small if and only if its classifying type `BG` is small. This
observation implies that an ∞-group `G` is small if and only if it is
{{#concept "structurally small" Disambiguation="∞-group" Agda=is-structurally-small-∞-Group}}
in the sense that it comes equipped with an element of type

```text
  Σ (H : ∞-Group), G ≃ H,
```

where the type `G ≃ H` is the type of
[equivalences of ∞-groups](higher-group-theory.equivalences-higher-groups.md).

Finally, we also introduce the notion of _pointed small ∞-group_. An ∞-group `G`
is said to be
{{#concept "pointed small" Disambiguation="∞-group" Agda=is-pointed-small-∞-Group}}
if its classifying [pointed type](structured-types.pointed-types.md) `BG` is
[pointed small](structured-types.small-pointed-types.md).

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

### The predicate of being a structurally small ∞-group

```agda
module _
  {l1 : Level} (l2 : Level) (G : ∞-Group l1)
  where

  is-structurally-small-∞-Group : UU (l1 ⊔ lsuc l2)
  is-structurally-small-∞-Group =
    Σ (∞-Group l2) (equiv-∞-Group G)

  abstract
    is-prop-is-structurally-small-∞-Group :
      is-prop is-structurally-small-∞-Group
    is-prop-is-structurally-small-∞-Group =
      is-prop-equiv
        ( equiv-right-swap-Σ)
        ( is-prop-Σ
          ( is-prop-is-pointed-small-Pointed-Type
            ( classifying-pointed-type-∞-Group G))
          ( λ H → is-prop-is-0-connected _))

  is-structurally-small-prop-∞-Group : Prop (l1 ⊔ lsuc l2)
  pr1 is-structurally-small-prop-∞-Group = is-structurally-small-∞-Group
  pr2 is-structurally-small-prop-∞-Group = is-prop-is-structurally-small-∞-Group

module _
  {l1 l2 : Level} (G : ∞-Group l1) (H : is-structurally-small-∞-Group l2 G)
  where

  ∞-group-is-structurally-small-∞-Group : ∞-Group l2
  ∞-group-is-structurally-small-∞-Group = pr1 H

  type-∞-group-is-structurally-small-∞-Group : UU l2
  type-∞-group-is-structurally-small-∞-Group =
    type-∞-Group ∞-group-is-structurally-small-∞-Group

  equiv-∞-group-is-structurally-small-∞-Group :
    equiv-∞-Group G ∞-group-is-structurally-small-∞-Group
  equiv-∞-group-is-structurally-small-∞-Group = pr2 H

  equiv-is-structurally-small-∞-Group :
    type-∞-Group G ≃ type-∞-group-is-structurally-small-∞-Group
  equiv-is-structurally-small-∞-Group =
    equiv-equiv-∞-Group G
      ( ∞-group-is-structurally-small-∞-Group)
      ( equiv-∞-group-is-structurally-small-∞-Group)
```

### The predicate of being a pointed small ∞-group

```agda
module _
  {l1 : Level} (l2 : Level) (G : ∞-Group l1)
  where

  is-pointed-small-prop-∞-Group : Prop (l1 ⊔ lsuc l2)
  is-pointed-small-prop-∞-Group =
    is-pointed-small-prop-Pointed-Type l2 (classifying-pointed-type-∞-Group G)

  is-pointed-small-∞-Group : UU (l1 ⊔ lsuc l2)
  is-pointed-small-∞-Group =
    is-pointed-small-Pointed-Type l2 (classifying-pointed-type-∞-Group G)

  is-prop-is-pointed-small-∞-Group : is-prop is-pointed-small-∞-Group
  is-prop-is-pointed-small-∞-Group =
    is-prop-is-pointed-small-Pointed-Type (classifying-pointed-type-∞-Group G)
```

## Properties

### The classifying type of any small ∞-group is locally small

```agda
module _
  {l1 l2 : Level} (G : ∞-Group l1) (H : is-small-∞-Group l2 G)
  where

  abstract
    is-locally-small-classifying-type-is-small-∞-Group' :
      (x y : classifying-type-∞-Group G) →
      shape-∞-Group G ＝ x → shape-∞-Group G ＝ y →
      is-small l2 (x ＝ y)
    is-locally-small-classifying-type-is-small-∞-Group' ._ ._ refl refl = H

  abstract
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

  abstract
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

  abstract
    is-small-is-small-classifying-type-∞-Group :
      is-small l2 (classifying-type-∞-Group G) → is-small-∞-Group l2 G
    is-small-is-small-classifying-type-∞-Group H =
      is-locally-small-is-small H (shape-∞-Group G) (shape-∞-Group G)
```

### An ∞-group is small if and only if it is pointed small

```agda
module _
  {l1 l2 : Level} (G : ∞-Group l1)
  where

  abstract
    is-pointed-small-is-small-∞-Group :
      is-small-∞-Group l2 G → is-pointed-small-∞-Group l2 G
    is-pointed-small-is-small-∞-Group H =
      is-pointed-small-is-small-Pointed-Type
        ( classifying-pointed-type-∞-Group G)
        ( is-small-classifying-type-is-small-∞-Group G H)
```

### An ∞-group is small if and only if it is structurally small

```agda
module _
  {l1 l2 : Level} (G : ∞-Group l1)
  where

  classifying-pointed-type-is-small-∞-Group :
    is-small-∞-Group l2 G → Pointed-Type l2
  classifying-pointed-type-is-small-∞-Group H =
    pointed-type-is-pointed-small-Pointed-Type
      ( classifying-pointed-type-∞-Group G)
      ( is-pointed-small-is-small-∞-Group G H)

  classifying-type-is-small-∞-Group : is-small-∞-Group l2 G → UU l2
  classifying-type-is-small-∞-Group H =
    type-is-pointed-small-Pointed-Type
      ( classifying-pointed-type-∞-Group G)
      ( is-pointed-small-is-small-∞-Group G H)

  abstract
    is-0-connected-classifying-type-is-small-∞-Group :
      (H : is-small-∞-Group l2 G) →
      is-0-connected (classifying-type-is-small-∞-Group H)
    is-0-connected-classifying-type-is-small-∞-Group H =
      is-0-connected-equiv'
        ( equiv-is-pointed-small-Pointed-Type
          ( classifying-pointed-type-∞-Group G)
          ( is-pointed-small-is-small-∞-Group G H))
        ( is-0-connected-classifying-type-∞-Group G)

  ∞-group-is-small-∞-Group : is-small-∞-Group l2 G → ∞-Group l2
  pr1 (∞-group-is-small-∞-Group H) =
    classifying-pointed-type-is-small-∞-Group H
  pr2 (∞-group-is-small-∞-Group H) =
    is-0-connected-classifying-type-is-small-∞-Group H

  pointed-type-∞-group-is-small-∞-Group :
    is-small-∞-Group l2 G → Pointed-Type l2
  pointed-type-∞-group-is-small-∞-Group H =
    pointed-type-∞-Group (∞-group-is-small-∞-Group H)

  type-∞-group-is-small-∞-Group :
    is-small-∞-Group l2 G → UU l2
  type-∞-group-is-small-∞-Group H =
    type-∞-Group (∞-group-is-small-∞-Group H)

  equiv-∞-group-is-small-∞-Group :
    (H : is-small-∞-Group l2 G) → equiv-∞-Group G (∞-group-is-small-∞-Group H)
  equiv-∞-group-is-small-∞-Group H =
    pointed-equiv-is-pointed-small-Pointed-Type
      ( classifying-pointed-type-∞-Group G)
      ( is-pointed-small-is-small-∞-Group G H)

  pointed-equiv-equiv-∞-group-is-small-∞-Group :
    (H : is-small-∞-Group l2 G) →
    pointed-type-∞-Group G ≃∗ pointed-type-∞-group-is-small-∞-Group H
  pointed-equiv-equiv-∞-group-is-small-∞-Group H =
    pointed-equiv-equiv-∞-Group G
      ( ∞-group-is-small-∞-Group H)
      ( equiv-∞-group-is-small-∞-Group H)

  equiv-equiv-∞-group-is-small-∞-Group :
    (H : is-small-∞-Group l2 G) →
    type-∞-Group G ≃ type-∞-group-is-small-∞-Group H
  equiv-equiv-∞-group-is-small-∞-Group H =
    equiv-equiv-∞-Group G
      ( ∞-group-is-small-∞-Group H)
      ( equiv-∞-group-is-small-∞-Group H)

  abstract
    is-structurally-small-is-small-∞-Group :
      is-small-∞-Group l2 G → is-structurally-small-∞-Group l2 G
    pr1 (is-structurally-small-is-small-∞-Group H) =
      ∞-group-is-small-∞-Group H
    pr2 (is-structurally-small-is-small-∞-Group H) =
      equiv-∞-group-is-small-∞-Group H

  abstract
    is-small-is-structurally-small-∞-Group :
      is-structurally-small-∞-Group l2 G → is-small-∞-Group l2 G
    pr1 (is-small-is-structurally-small-∞-Group H) =
      type-∞-group-is-structurally-small-∞-Group G H
    pr2 (is-small-is-structurally-small-∞-Group H) =
      equiv-is-structurally-small-∞-Group G H

  abstract
    is-small-∞-group-is-small-∞-Group :
      (H : is-small-∞-Group l2 G) →
      is-small-∞-Group l1 (∞-group-is-small-∞-Group H)
    pr1 (is-small-∞-group-is-small-∞-Group H) = type-∞-Group G
    pr2 (is-small-∞-group-is-small-∞-Group H) =
      inv-equiv (equiv-equiv-∞-group-is-small-∞-Group H)
```
