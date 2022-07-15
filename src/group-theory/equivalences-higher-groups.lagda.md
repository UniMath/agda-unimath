---
title: Equivalences of higher groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.equivalences-higher-groups where

open import foundation.functions
open import foundation.universe-levels

open import group-theory.higher-groups
open import group-theory.homomorphisms-higher-groups

open import structured-types.pointed-equivalences
```

## Definitions

### Equivalences of higher groups

```agda
module _
  {l1 l2 : Level} (G : ∞-Group l1) (H : ∞-Group l2)
  where

  equiv-∞-Group : UU (l1 ⊔ l2)
  equiv-∞-Group =
    classifying-pointed-type-∞-Group G ≃* classifying-pointed-type-∞-Group H

  hom-equiv-∞-Group : equiv-∞-Group → hom-∞-Group G H
  hom-equiv-∞-Group =
    pointed-map-pointed-equiv
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)

  map-equiv-∞-Group : equiv-∞-Group → type-∞-Group G → type-∞-Group H
  map-equiv-∞-Group = map-hom-∞-Group G H ∘ hom-equiv-∞-Group
```

### The identity equivalence of higher groups

```agda
id-equiv-∞-Group :
  {l1 : Level} (G : ∞-Group l1) → equiv-∞-Group G G
id-equiv-∞-Group G = id-pointed-equiv (classifying-pointed-type-∞-Group G)
```
