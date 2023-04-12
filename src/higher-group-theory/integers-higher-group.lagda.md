# The higher group of integers

```agda
module higher-group-theory.integers-higher-group where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import higher-group-theory.higher-groups

open import structured-types.pointed-types

open import synthetic-homotopy-theory.circle
```

</details>

## Idea

The higher group of integers is defined to be the circle. The loop space of the
circle is ℤ.

## Definition

```agda
module _
  where

  classifying-type-ℤ-∞-Group : UU lzero
  classifying-type-ℤ-∞-Group = 𝕊¹

  shape-ℤ-∞-Group : 𝕊¹
  shape-ℤ-∞-Group = base-𝕊¹

  classifying-pointed-type-ℤ-∞-Group : Pointed-Type lzero
  pr1 classifying-pointed-type-ℤ-∞-Group = classifying-type-ℤ-∞-Group
  pr2 classifying-pointed-type-ℤ-∞-Group = shape-ℤ-∞-Group

  ℤ-∞-Group : ∞-Group lzero
  pr1 ℤ-∞-Group = classifying-pointed-type-ℤ-∞-Group
  pr2 ℤ-∞-Group = is-0-connected-𝕊¹
```
