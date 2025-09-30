# The flattening morphisms from free magmas to free monoids

```agda
module lists.flattening-free-magmas-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies

open import lists.concatenation-lists
open import lists.lists
open import lists.universal-property-lists-wild-monoids

open import structured-types.magmas
open import structured-types.morphisms-h-spaces
open import structured-types.morphisms-magmas
open import structured-types.morphisms-wild-monoids
open import structured-types.pointed-maps
open import structured-types.wild-monoids

open import trees.combinator-full-binary-trees
open import trees.free-magmas-on-types
open import trees.full-binary-trees
open import trees.labeled-full-binary-trees
```

</details>

## Idea

For any type `X`, there is a natural
[magma map](structured-types.morphisms-magmas.md) from
`labeled-full-binary-tree-Magma X`, the
[free magma on `X`](trees.free-magmas-on-types.md), to `list-Wild-Monoid X`, the
[free wild monoid on `X`](lists.universal-property-lists-wild-monoids.md), that
can be thought of as forgetting the tree structure and remembering the order
leaves are read off in. This map is universal among magma maps from
`labeled-full-binary-tree-Magma X` to
[wild monoids](structured-types.wild-monoids.md).

## Definition

```agda
module _
  {l : Level} (X : UU l)
  where

  {-# TERMINATING #-}
  flattening-map-free-Magma-free-Wild-Monoid :
    type-Magma (labeled-full-binary-tree-Magma X) →
    type-Wild-Monoid (list-Wild-Monoid X)
  flattening-map-free-Magma-free-Wild-Monoid (leaf-full-binary-tree , label) =
    cons (label star) nil
  flattening-map-free-Magma-free-Wild-Monoid
    (join-full-binary-tree L R , label) =
      concat-list
      ( flattening-map-free-Magma-free-Wild-Monoid (L , λ z → label (inl z)))
      ( flattening-map-free-Magma-free-Wild-Monoid (R , (λ z → label (inr z))))

  preserves-mul-flattening-map-free-Magma-free-Wild-Monoid :
    preserves-mul-Magma (labeled-full-binary-tree-Magma X)
    (magma-Wild-Monoid (list-Wild-Monoid X))
    flattening-map-free-Magma-free-Wild-Monoid
  preserves-mul-flattening-map-free-Magma-free-Wild-Monoid T U = refl

  flattening-hom-free-Magma-free-Wild-Monoid :
    hom-Magma (labeled-full-binary-tree-Magma X)
    (magma-Wild-Monoid (list-Wild-Monoid X))
  pr1 flattening-hom-free-Magma-free-Wild-Monoid =
    flattening-map-free-Magma-free-Wild-Monoid
  pr2 flattening-hom-free-Magma-free-Wild-Monoid =
    preserves-mul-flattening-map-free-Magma-free-Wild-Monoid
```

## Properties

### The flattening map preserves weights

That is, the length of a flattened full binary tree `T` is equal to the weight
of `T`.

```agda
  preserves-weight-flattening-hom-free-Magma-free-Wild-Monoid :
    (T : labeled-full-binary-tree X) →
    length-list (flattening-map-free-Magma-free-Wild-Monoid T) ＝
    weight-labeled-full-binary-tree X T
  preserves-weight-flattening-hom-free-Magma-free-Wild-Monoid
    (leaf-full-binary-tree , label) =
      refl
  preserves-weight-flattening-hom-free-Magma-free-Wild-Monoid
    (join-full-binary-tree L R , label) =
      ap-binary add-ℕ refl refl
```

### The flattening map is the universal map from `labeled-full-binary-tree-Magma X` to a wild monoid

More precisely, for any wild monoid `M` and magma map
`f : labeled-full-binary-tree-Magma X → M`, the space of monoid maps
`list-Wild-Monoid X → M` commuting with the flattening map is contractible.

```agda
module _
  {l1 l2 : Level} (X : UU l1) (M : Wild-Monoid l2)
  where

  extension-flattening-map-free-Magma-free-Wild-Monoid :
    (f : hom-Magma (labeled-full-binary-tree-Magma X) (magma-Wild-Monoid M)) →
    hom-Wild-Monoid (list-Wild-Monoid X) M
  extension-flattening-map-free-Magma-free-Wild-Monoid f =
    elim-list-Wild-Monoid M (label-of-leaf X (magma-Wild-Monoid M) f)

  extension-flattening-map-commutes-free-Magma-free-Wild-Monoid :
    (f : hom-Magma (labeled-full-binary-tree-Magma X) (magma-Wild-Monoid M)) →
    map-hom-Magma (labeled-full-binary-tree-Magma X) (magma-Wild-Monoid M) f ~
    map-hom-Wild-Monoid (list-Wild-Monoid X) M
      (extension-flattening-map-free-Magma-free-Wild-Monoid f) ∘
    flattening-map-free-Magma-free-Wild-Monoid X
  extension-flattening-map-commutes-free-Magma-free-Wild-Monoid
    (f , hom-f) (leaf-full-binary-tree , label) =
      {!   !}
  extension-flattening-map-commutes-free-Magma-free-Wild-Monoid
    (f , hom-f) (join-full-binary-tree L R , label) =
      {!   !}
```
