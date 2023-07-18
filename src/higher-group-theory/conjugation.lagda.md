# Conjugation in higher groups

```agda
module higher-group-theory.conjugation where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import higher-group-theory.higher-groups
open import higher-group-theory.homomorphisms-higher-groups

open import structured-types.conjugation-pointed-types
```

</details>

## Idea

The **conjugation homomorphism** on an
[∞-group](higher-group-theory.higher-groups.md) `G` is the
[conjugation map](structured-types.conjugation-pointed-types.md) of its
classifying [pointed type](structured-types.pointed-types.md) `BG`.

## Definition

```agda
module _
  {l : Level} (G : ∞-Group l)
  where

  conjugation-∞-Group : type-∞-Group G → hom-∞-Group G G
  conjugation-∞-Group =
    conjugation-Pointed-Type (classifying-pointed-type-∞-Group G)
```
