# The higher group of integers

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module higher-group-theory.integers-higher-group
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import higher-group-theory.higher-groups funext univalence truncations

open import structured-types.pointed-types

open import synthetic-homotopy-theory.circle funext univalence truncations
```

</details>

## Idea

The **higher group of integers** is defined to be the
[circle](synthetic-homotopy-theory.circle.md). The
[loop space](synthetic-homotopy-theory.loop-spaces.md) of the circle is
[`ℤ`](elementary-number-theory.integers.md).

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
