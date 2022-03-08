# Natural isomorphisms between functors on precategories

```agda
{-# OPTIONS --without-K --exact-split #-}

module categories.natural-isomorphisms-precategories where

open import categories.functors-precategories using (functor-Precat)
open import categories.isomorphisms-precategories using
  ( is-iso-Precat; is-prop-is-iso-Precat)
open import categories.natural-transformations-precategories using
  ( nat-trans-Precat; components-nat-trans-Precat)
open import categories.precategories using (Precat; obj-Precat)
open import foundation.dependent-pair-types using (Σ)
open import foundation.propositions using (is-prop; is-prop-Π)
open import foundation.universe-levels using (UU; _⊔_)
```

## Idea

A natural isomorphism `γ` from functor `F : C → D` to `G : C → D` is a natural transformation from `F` to `G` such that the morphism `γ x : hom (F x) (G x)` is an isomorphism, for every object `x` in `C`.

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
