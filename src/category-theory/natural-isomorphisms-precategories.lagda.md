# Natural isomorphisms between functors between precategories

```agda
module category-theory.natural-isomorphisms-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.isomorphisms-precategories
open import category-theory.natural-transformations-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A natural isomorphism `γ` from functor `F : C → D` to `G : C → D` is a natural
transformation from `F` to `G` such that the morphism `γ x : hom (F x) (G x)` is
an isomorphism, for every object `x` in `C`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precat l1 l2)
  (D : Precat l3 l4)
  (F G : functor-Precat C D)
  where

  is-natural-isomorphism-Precat :
    natural-transformation-Precat C D F G → UU (l1 ⊔ l4)
  is-natural-isomorphism-Precat γ =
    (x : obj-Precat C) →
    is-iso-Precat D (components-natural-transformation-Precat C D F G γ x)

  natural-isomorphism-Precat : UU (l1 ⊔ l2 ⊔ l4)
  natural-isomorphism-Precat =
    Σ (natural-transformation-Precat C D F G) is-natural-isomorphism-Precat
```

## Propositions

### Being a natural isomorphism is a proposition

That a natural transformation is a natural isomorphism is a proposition. This
follows from the fact that being an isomorphism is a proposition.

```agda
is-prop-is-natural-isomorphism-Precat :
  {l1 l2 l3 l4 : Level}
  (C : Precat l1 l2)
  (D : Precat l3 l4)
  (F G : functor-Precat C D)
  (γ : natural-transformation-Precat C D F G) →
  is-prop (is-natural-isomorphism-Precat C D F G γ)
is-prop-is-natural-isomorphism-Precat C D F G γ =
  is-prop-Π (is-prop-is-iso-Precat D ∘
  components-natural-transformation-Precat C D F G γ)
```
