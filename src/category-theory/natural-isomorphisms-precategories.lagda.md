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
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A natural isomorphism `γ` from functor `F : C → D` to `G : C → D` is a natural transformation from `F` to `G` such that the morphism `γ x : hom (F x) (G x)` is an isomorphism, for every object `x` in `C`.

## Definition

```agda
module _ {l1 l2 l3 l4}
  (C : Precat l1 l2)
  (D : Precat l3 l4)
  (F G : functor-Precat C D) where

  is-nat-iso-Precat : nat-trans-Precat C D F G → UU (l1 ⊔ l4)
  is-nat-iso-Precat γ = (x : obj-Precat C) → is-iso-Precat D (components-nat-trans-Precat C D F G γ x)

  nat-iso-Precat : UU (l1 ⊔ l2 ⊔ l4)
  nat-iso-Precat =
    Σ (nat-trans-Precat C D F G) is-nat-iso-Precat
```

## Propositions

### Being a natural isomorphism is a proposition

That a natural transformation is a natural isomorphism is a proposition. This follows from the fact that being an isomorphism is a proposition.

```agda
is-prop-is-nat-iso-Precat :
  ∀ {l1 l2 l3 l4} →
  (C : Precat l1 l2) →
  (D : Precat l3 l4) →
  (F G : functor-Precat C D) →
  (γ : nat-trans-Precat C D F G) →
  is-prop (is-nat-iso-Precat C D F G γ)
is-prop-is-nat-iso-Precat C D F G γ =
  is-prop-Π (λ x → is-prop-is-iso-Precat D (components-nat-trans-Precat C D F G γ x))
```
