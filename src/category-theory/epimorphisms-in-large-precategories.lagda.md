# Epimorphism in large precategories

```agda
module category-theory.epimorphisms-in-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories
open import category-theory.large-precategories

open import foundation.dependent-products-propositions
open import foundation.embeddings
open import foundation.equivalences
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A morphism `f : x → y` is a epimorphism if whenever we have two morphisms
`g h : y → w` such that `g ∘ f = h ∘ f`, then in fact `g = h`. The way to state
this in Homotopy Type Theory is to say that precomposition by `f` is an
embedding.

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level} (l3 : Level)
  (X : obj-Large-Precategory C l1) (Y : obj-Large-Precategory C l2)
  (f : hom-Large-Precategory C X Y)
  where

  is-epi-prop-Large-Precategory : Prop (α l3 ⊔ β l1 l3 ⊔ β l2 l3)
  is-epi-prop-Large-Precategory =
    Π-Prop
      ( obj-Large-Precategory C l3)
      ( λ Z → is-emb-Prop (λ g → comp-hom-Large-Precategory C {Z = Z} g f))

  is-epi-Large-Precategory : UU (α l3 ⊔ β l1 l3 ⊔ β l2 l3)
  is-epi-Large-Precategory = type-Prop is-epi-prop-Large-Precategory

  is-prop-is-epi-Large-Precategory : is-prop is-epi-Large-Precategory
  is-prop-is-epi-Large-Precategory =
    is-prop-type-Prop is-epi-prop-Large-Precategory
```

## Properties

### Isomorphisms are epimorphisms

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level} (l3 : Level)
  (X : obj-Large-Precategory C l1) (Y : obj-Large-Precategory C l2)
  (f : iso-Large-Precategory C X Y)
  where

  is-epi-iso-Large-Precategory :
    is-epi-Large-Precategory C l3 X Y (hom-iso-Large-Precategory C f)
  is-epi-iso-Large-Precategory Z =
    is-emb-is-equiv (is-equiv-precomp-hom-iso-Large-Precategory C f Z)
```
