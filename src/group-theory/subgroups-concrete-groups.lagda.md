---
title: Subgroups of concrete groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.subgroups-concrete-groups where

open import foundation.dependent-pair-types using (Σ)
open import foundation.embeddings using (is-emb-Prop)
open import foundation.propositions using
  ( UU-Prop; Π-Prop; type-Prop; is-prop; is-prop-type-Prop)
open import foundation.universe-levels using (UU; Level; _⊔_; lsuc)
open import group-theory.concrete-groups using
  ( Concrete-Group; hom-Concrete-Group; comp-hom-Concrete-Group)
```

## Idea

A concrete subgroup of a concrete group BG consists of a concrete group BH equipped with a faithful pointed map BH →* BG. Recall that a map is said to be faithful if it induces embeddings on identity types. In particular, any faithful pointed map BH →* BG induces an embedding ΩBH → ΩBG, i.e., an inclusion of the underlying groups of a concrete group. Faithful pointed maps BH →* BG are equivalently described as monomorphisms in the category of concrete groups.

```agda
module _ {l1 l2 : Level} (l3 : Level)
  (G : Concrete-Group l1) (H : Concrete-Group l2)
  (f : hom-Concrete-Group G H) where

  is-mono-hom-Concrete-Group-Prop : UU-Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-mono-hom-Concrete-Group-Prop =
    Π-Prop
      ( Concrete-Group l3)
      ( λ F → is-emb-Prop (comp-hom-Concrete-Group F G H f))

  is-mono-hom-Concrete-Group : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-mono-hom-Concrete-Group = type-Prop is-mono-hom-Concrete-Group-Prop

  is-prop-is-mono-hom-Concrete-Group : is-prop is-mono-hom-Concrete-Group
  is-prop-is-mono-hom-Concrete-Group =
    is-prop-type-Prop is-mono-hom-Concrete-Group-Prop

module _ {l1 : Level} (l2 : Level) (G : Concrete-Group l1) where

  mono-Concrete-Group : UU (l1 ⊔ lsuc l2)
  mono-Concrete-Group =
    Σ ( Concrete-Group l2)
      ( λ H →
        Σ (hom-Concrete-Group H G) λ f → is-mono-hom-Concrete-Group l2 H G f)
```
