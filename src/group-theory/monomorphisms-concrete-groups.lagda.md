# Monomorphisms of concrete groups

```agda
module group-theory.monomorphisms-concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.homomorphisms-concrete-groups
```

</details>

## Idea

A monomorphism of concrete groups from `G` to `H` is a faithful pointed map BH
→∗ BG. Recall that a map is said to be faithful if it induces embeddings on
identity types. In particular, any faithful pointed map BH →∗ BG induces an
embedding ΩBH → ΩBG, i.e., an inclusion of the underlying groups of a concrete
group.

```agda
module _
  {l1 l2 : Level} (l3 : Level)
  (G : Concrete-Group l1) (H : Concrete-Group l2)
  (f : hom-Concrete-Group G H)
  where

  is-mono-prop-hom-Concrete-Group : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-mono-prop-hom-Concrete-Group =
    Π-Prop
      ( Concrete-Group l3)
      ( λ F → is-emb-Prop (comp-hom-Concrete-Group F G H f))

  is-mono-hom-Concrete-Group : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-mono-hom-Concrete-Group = type-Prop is-mono-prop-hom-Concrete-Group

  is-prop-is-mono-hom-Concrete-Group : is-prop is-mono-hom-Concrete-Group
  is-prop-is-mono-hom-Concrete-Group =
    is-prop-type-Prop is-mono-prop-hom-Concrete-Group

module _
  {l1 : Level} (l2 : Level) (G : Concrete-Group l1)
  where

  mono-Concrete-Group : UU (l1 ⊔ lsuc l2)
  mono-Concrete-Group =
    Σ ( Concrete-Group l2)
      ( λ H →
        Σ (hom-Concrete-Group H G) λ f → is-mono-hom-Concrete-Group l2 H G f)
```
