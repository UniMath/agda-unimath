---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module subgroups.concrete-subgroups where

open import groups.concrete-groups public

is-mono-hom-Concrete-Group : {l : Level}
                           → (G H : Concrete-Group l)
                           → hom-Concrete-Group G H
                           → UU (lsuc l)
is-mono-hom-Concrete-Group {l} G H f =
  (F : Concrete-Group l) → is-injective (comp-hom-Concrete-Group F G H f)

module _ {l1 : Level} (G : Concrete-Group l1) where

  mono-Concrete-Group : UU (lsuc l1)
  mono-Concrete-Group =
    Σ (Concrete-Group l1) (λ H → Σ (hom-Concrete-Group H G) λ f → is-mono-hom-Concrete-Group H G f)
```
