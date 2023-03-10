# Symmetric higher groups

```agda
module group-theory.symmetric-higher-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.connected-components-universes
open import foundation.dependent-pair-types
open import foundation.mere-equivalences
open import foundation.universe-levels

open import group-theory.higher-groups

open import structured-types.pointed-types
```

</details>

## Idea

The symmetric higher group of a type `X` is the connected component of the universe at `X`.

## Definition

```agda
module _
  {l : Level} (X : UU l)
  where

  classifying-type-symmetric-∞-Group : UU (lsuc l)
  classifying-type-symmetric-∞-Group = component-UU X

  shape-symmetric-∞-Group : classifying-type-symmetric-∞-Group
  shape-symmetric-∞-Group =
    pair X (refl-mere-equiv X)

  classifying-pointed-type-symmetric-∞-Group : Pointed-Type (lsuc l)
  classifying-pointed-type-symmetric-∞-Group =
    pair
      classifying-type-symmetric-∞-Group
      shape-symmetric-∞-Group

  is-0-connected-classifying-type-symmetric-∞-Group :
    is-0-connected classifying-type-symmetric-∞-Group
  is-0-connected-classifying-type-symmetric-∞-Group =
    is-0-connected-component-UU X

  symmetric-∞-Group : ∞-Group (lsuc l)
  symmetric-∞-Group =
    pair
      classifying-pointed-type-symmetric-∞-Group
      is-0-connected-classifying-type-symmetric-∞-Group
```
