# Symmetric higher groups

```agda
open import foundation.function-extensionality-axiom

module
  higher-group-theory.symmetric-higher-groups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types funext
open import foundation.connected-components-universes funext
open import foundation.dependent-pair-types
open import foundation.mere-equivalences funext
open import foundation.universe-levels

open import higher-group-theory.higher-groups funext

open import structured-types.pointed-types
```

</details>

## Idea

The symmetric higher group of a type `X` is the connected component of the
universe at `X`.

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
