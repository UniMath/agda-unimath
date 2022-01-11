---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module subgroups.concrete-subgroups where

open import groups.concrete-groups public

module _ {l1 l2 : Level} (l3 : Level)
  (G : Concrete-Group l1) (H : Concrete-Group l2)
  (f : hom-Concrete-Group G H) where

  is-mono-hom-Concrete-Group-Prop : UU-Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-mono-hom-Concrete-Group-Prop =
    Π-Prop (Concrete-Group l3) (λ F → is-emb-Prop (comp-hom-Concrete-Group F G H f))

  is-mono-hom-Concrete-Group : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-mono-hom-Concrete-Group = type-Prop is-mono-hom-Concrete-Group-Prop

  is-prop-is-mono-hom-Concrete-Group : is-prop is-mono-hom-Concrete-Group
  is-prop-is-mono-hom-Concrete-Group = is-prop-type-Prop is-mono-hom-Concrete-Group-Prop

module _ {l1 : Level} (l2 : Level) (G : Concrete-Group l1) where

  mono-Concrete-Group : UU (l1 ⊔ lsuc l2)
  mono-Concrete-Group =
    Σ (Concrete-Group l2) (λ H → Σ (hom-Concrete-Group H G) λ f → is-mono-hom-Concrete-Group l2 H G f)
```

TODO:
  * prove that mono-Concrete-Group is a set
  * define type of subgroups using G-sets
  * prove that the two types are equivalent
