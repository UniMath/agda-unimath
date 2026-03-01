# Globular pasting schemes

```agda
{-# OPTIONS --guardedness #-}

module globular-types.globular-pasting-schemes where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.maybe
open import foundation.unit-type
open import foundation.universe-levels

open import globular-types.empty-globular-types
open import globular-types.globular-disks
open import globular-types.globular-types

open import lists.lists

open import trees.plane-trees
```

</details>

## Idea

Consider a [plane tree](trees.plane-trees.md) `T` such as

```text
  *       *     *
   \     /      |
    \   /       |
     \ /        |
      *    *    *
       \   |   /
        \  |  /
         \ | /
           *
```

The
{{#concept "globular pasting scheme" Disambiguation="globular type" Agda=pasting-scheme-Globular-Type}}
of shape `T` is a [globular type](globular-types.globular-types.md) defined
inductively on the shape of `T` as follows:

- If `T = nil`, then the pasting scheme of shape `T` is a representing 0-cell.
  That is, a pasting scheme of shape nil is the
  [0-disk](globular-types.globular-disks.md).
- If `T = S ∷ ℓ`, where `ℓ` is a [list](lists.lists.md) of plane trees, then the
  pasting scheme of shape `T` consists a 0-cell `x₀`, the pasting scheme of
  shape `ℓ` seen as a plane tree, which has an initial 0-cell `x₁`, and the
  globular type of `1`-cells between `x₀` and `x₁` is the pasting scheme of
  shape `T`.

In other words, a globular pasting scheme is a representing object for
[globular pasting diagrams](globular-types.globular-pasting-diagrams.md) of its
shape. The example plane tree `T` displayed above gives the following pasting
scheme:

```text
     _____
    /  ∥  \             ______
   /   ∨   ∨           /  ∥   ∨
  * ------> * ------> *   ∥    *
   \   ∥    ∧          \  ∨   ∧
    \  ∨   /            ------
     -----
```

## Definitions

### Pasting schemes

```agda
module _
  where

  pasting-scheme-Globular-Type :
    (T : listed-plane-tree) → Globular-Type lzero lzero
  pasting-scheme-Globular-Type (make-listed-plane-tree nil) =
    globular-0-disk
  0-cell-Globular-Type (pasting-scheme-Globular-Type
    ( make-listed-plane-tree (cons T ℓ))) =
    Maybe
      ( 0-cell-Globular-Type
        ( pasting-scheme-Globular-Type (make-listed-plane-tree ℓ)))
  1-cell-globular-type-Globular-Type
    ( pasting-scheme-Globular-Type (make-listed-plane-tree (cons T nil)))
    ( inl x)
    ( inl y) =
    empty-Globular-Type
  1-cell-globular-type-Globular-Type
    ( pasting-scheme-Globular-Type (make-listed-plane-tree (cons T nil)))
    ( inl x)
    ( inr y) =
    empty-Globular-Type
  1-cell-globular-type-Globular-Type
    ( pasting-scheme-Globular-Type (make-listed-plane-tree (cons T nil)))
    ( inr x)
    ( inl y) =
    pasting-scheme-Globular-Type T
  1-cell-globular-type-Globular-Type
    ( pasting-scheme-Globular-Type (make-listed-plane-tree (cons T nil)))
    ( inr x)
    ( inr y) =
    empty-Globular-Type
  1-cell-globular-type-Globular-Type
    ( pasting-scheme-Globular-Type
      ( make-listed-plane-tree (cons S (cons T ℓ))))
    ( inl x)
    ( inl y) =
    1-cell-globular-type-Globular-Type
      ( pasting-scheme-Globular-Type (make-listed-plane-tree (cons T ℓ))) x y
  1-cell-globular-type-Globular-Type
    ( pasting-scheme-Globular-Type
      ( make-listed-plane-tree (cons S (cons T ℓ))))
    ( inl x)
    ( inr y) =
    empty-Globular-Type
  1-cell-globular-type-Globular-Type
    ( pasting-scheme-Globular-Type
      ( make-listed-plane-tree (cons S (cons T ℓ))))
    ( inr x)
    ( inl (inl y)) = empty-Globular-Type
  1-cell-globular-type-Globular-Type
    ( pasting-scheme-Globular-Type
      ( make-listed-plane-tree (cons S (cons T ℓ))))
    ( inr x)
    ( inl (inr y)) =
    pasting-scheme-Globular-Type S
  1-cell-globular-type-Globular-Type
    ( pasting-scheme-Globular-Type
      ( make-listed-plane-tree (cons S (cons T ℓ))))
    ( inr x)
    ( inr y) =
    empty-Globular-Type
```
