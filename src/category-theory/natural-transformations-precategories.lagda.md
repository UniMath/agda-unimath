# Natural transformations between functors on precategories

```agda
{-# OPTIONS --without-K --exact-split #-}

module category-theory.natural-transformations-precategories where

open import category-theory.functors-precategories using
  (functor-Precat; obj-functor-Precat; hom-functor-Precat)
open import category-theory.precategories using
  ( Precat; obj-Precat; type-hom-Precat; comp-hom-Precat;
    is-set-type-hom-Precat)
open import foundation.dependent-pair-types using (Σ; pr1)
open import foundation.identity-types using (Id)
open import foundation.propositions using
  ( is-prop; is-prop-Π; is-prop-Π')
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

Given precategories `C` and `D`, a natural transformation from a functor `F : C → D` to `G : C → D` consists of :
- a family of morphisms `γ : (x : C) → hom (F x) (G x)`
such that the following identity holds:
- `comp (G f) (γ x) = comp (γ y) (F f)`, for all `f : hom x y`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precat l1 l2) (D : Precat l3 l4)
  (F G : functor-Precat C D)
  where

  is-nat-trans-Precat :
    ( (x : obj-Precat C) →
      type-hom-Precat D
        ( obj-functor-Precat C D F x)
        ( obj-functor-Precat C D G x)) →
    UU (l1 ⊔ l2 ⊔ l4)
  is-nat-trans-Precat γ =
    {x y : obj-Precat C} (f : type-hom-Precat C x y) →
    Id ( comp-hom-Precat D (hom-functor-Precat C D G f) (γ x))
       ( comp-hom-Precat D (γ y) (hom-functor-Precat C D F f))

  nat-trans-Precat : UU (l1 ⊔ l2 ⊔ l4)
  nat-trans-Precat =
    Σ ( (x : obj-Precat C) →
        type-hom-Precat D
          ( obj-functor-Precat C D F x)
          ( obj-functor-Precat C D G x))
      ( is-nat-trans-Precat)

  components-nat-trans-Precat :
    nat-trans-Precat → (x : obj-Precat C) →
    type-hom-Precat D (obj-functor-Precat C D F x) (obj-functor-Precat C D G x)
  components-nat-trans-Precat = pr1
```

## Properties

### That a family of morphisms is a natural transformation is a proposition

This follows from the fact that the hom-types are sets.

```agda
is-prop-is-nat-trans-Precat :
  { l1 l2 l3 l4 : Level} (C : Precat l1 l2) (D : Precat l3 l4)
  ( F G : functor-Precat C D) →
  ( γ :
    (x : obj-Precat C) →
    type-hom-Precat D
      ( obj-functor-Precat C D F x)
      ( obj-functor-Precat C D G x)) →
  is-prop (is-nat-trans-Precat C D F G γ)
is-prop-is-nat-trans-Precat C D F G γ =
  is-prop-Π'
    ( λ x →
      is-prop-Π'
        ( λ y →
          is-prop-Π
            ( λ f →
              is-set-type-hom-Precat D
                ( obj-functor-Precat C D F x)
                ( obj-functor-Precat C D G y)
                ( comp-hom-Precat D (hom-functor-Precat C D G f) (γ x))
                ( comp-hom-Precat D (γ y) (hom-functor-Precat C D F f)))))
```
