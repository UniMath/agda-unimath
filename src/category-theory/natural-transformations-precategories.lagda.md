# Natural transformations between functors on precategories

```agda
module category-theory.natural-transformations-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equational-reasoning
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

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
    ( comp-hom-Precat D (hom-functor-Precat C D G f) (γ x)) ＝
    ( comp-hom-Precat D (γ y) (hom-functor-Precat C D F f))

  nat-trans-Precat : UU (l1 ⊔ l2 ⊔ l4)
  nat-trans-Precat =
    Σ ( (x : obj-Precat C) →
        type-hom-Precat D
          ( obj-functor-Precat C D F x)
          ( obj-functor-Precat C D G x))
      is-nat-trans-Precat

  components-nat-trans-Precat :
    nat-trans-Precat → (x : obj-Precat C) →
    type-hom-Precat D (obj-functor-Precat C D F x) (obj-functor-Precat C D G x)
  components-nat-trans-Precat = pr1

  squares-nat-trans-Precat : (γ : nat-trans-Precat) → is-nat-trans-Precat (components-nat-trans-Precat γ)
  squares-nat-trans-Precat = pr2
```

## Composition and identity of natural transformations

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precat l1 l2) (D : Precat l3 l4)
  where

  id-nat-trans-Precat : (F : functor-Precat C D) → nat-trans-Precat C D F F
  pr1 (id-nat-trans-Precat F) = λ x → id-hom-Precat D
  pr2 (id-nat-trans-Precat F) = λ f → right-unit-law-comp-hom-Precat D _ ∙ inv (left-unit-law-comp-hom-Precat D _)

  comp-nat-trans-Precat :
     (F G H : functor-Precat C D) → nat-trans-Precat C D G H → nat-trans-Precat C D F G → nat-trans-Precat C D F H
  pr1 (comp-nat-trans-Precat F G H β α) =
    λ x → comp-hom-Precat D (components-nat-trans-Precat C D G H β x) (components-nat-trans-Precat C D F G α x)
  pr2 (comp-nat-trans-Precat F G H β α) f =
    equational-reasoning
       comp-hom-Precat D (hom-functor-Precat C D H f)
         (comp-hom-Precat D (components-nat-trans-Precat C D G H β _)
          (pr1 α _))
    ＝ comp-hom-Precat D
        (comp-hom-Precat D (hom-functor-Precat C D H f)
         (components-nat-trans-Precat C D G H β _))
        (pr1 α _)                                                  by inv (assoc-comp-hom-Precat D _ _ _)
    ＝ comp-hom-Precat D
        (comp-hom-Precat D (pr1 β _) (hom-functor-Precat C D G f))
        (components-nat-trans-Precat C D F G α _)                  by ap (λ x → comp-hom-Precat D x _) (squares-nat-trans-Precat C D G H β f)
    ＝ comp-hom-Precat D (pr1 β _)
        (comp-hom-Precat D (hom-functor-Precat C D G f)
         (components-nat-trans-Precat C D F G α _))                by assoc-comp-hom-Precat D _ _ _
    ＝ comp-hom-Precat D (pr1 β _)
        (comp-hom-Precat D (components-nat-trans-Precat C D F G α _)
         (hom-functor-Precat C D F f))                             by ap (λ x → comp-hom-Precat D _ x) (squares-nat-trans-Precat C D F G α f)
    ＝ comp-hom-Precat D
        (comp-hom-Precat D (pr1 β _)
         (components-nat-trans-Precat C D F G α _))
        (hom-functor-Precat C D F f)                               by inv (assoc-comp-hom-Precat D _ _ _)
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

is-nat-trans-Precat-Prop :
  { l1 l2 l3 l4 : Level} (C : Precat l1 l2) (D : Precat l3 l4)
  ( F G : functor-Precat C D) →
  ( γ :
    (x : obj-Precat C) →
    type-hom-Precat D
      ( obj-functor-Precat C D F x)
      ( obj-functor-Precat C D G x)) →
  Prop (l1 ⊔ l2 ⊔ l4)
is-nat-trans-Precat-Prop C D F G α = is-nat-trans-Precat C D F G α , is-prop-is-nat-trans-Precat C D F G α

components-nat-trans-Precat-is-emb :
  { l1 l2 l3 l4 : Level} (C : Precat l1 l2) (D : Precat l3 l4)
  ( F G : functor-Precat C D) →
  is-emb (components-nat-trans-Precat C D F G)
components-nat-trans-Precat-is-emb C D F G = is-emb-inclusion-subtype (λ α → is-nat-trans-Precat-Prop C D F G α)

nat-trans-Precat-Set :
  {l1 l2 l3 l4 : Level}(C : Precat l1 l2)(D : Precat l3 l4)(F G : functor-Precat C D) →
  Set (l1 ⊔ l2 ⊔ l4)
nat-trans-Precat-Set C D F G =
  nat-trans-Precat C D F G ,
  is-set-Σ
    (is-set-Π λ x → is-set-type-hom-Precat D (obj-functor-Precat C D F x) (obj-functor-Precat C D G x))
    λ α → pr2 (set-Prop (is-nat-trans-Precat-Prop C D F G α))
```

### Category laws for natural transformations

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precat l1 l2) (D : Precat l3 l4)
  where

  eq-nat-trans-Precat :
    (F G : functor-Precat C D)(α β : nat-trans-Precat C D F G) →
    (components-nat-trans-Precat C D F G α ＝ components-nat-trans-Precat C D F G β) →
    α ＝ β
  eq-nat-trans-Precat F G α β = is-injective-is-emb (components-nat-trans-Precat-is-emb C D F G)

  right-unit-law-comp-nat-trans-Precat :
    {F G : functor-Precat C D}(α : nat-trans-Precat C D F G)
    → comp-nat-trans-Precat C D F F G α (id-nat-trans-Precat C D F) ＝ α
  right-unit-law-comp-nat-trans-Precat {F} {G} α =
    eq-nat-trans-Precat F G (comp-nat-trans-Precat C D F F G α (id-nat-trans-Precat C D F)) α
    (eq-htpy λ x → right-unit-law-comp-hom-Precat D (components-nat-trans-Precat C D F G α x))

  left-unit-law-comp-nat-trans-Precat :
    {F G : functor-Precat C D}(α : nat-trans-Precat C D F G)
    → comp-nat-trans-Precat C D F G G (id-nat-trans-Precat C D G) α ＝ α
  left-unit-law-comp-nat-trans-Precat {F} {G} α =
    eq-nat-trans-Precat F G (comp-nat-trans-Precat C D F G G (id-nat-trans-Precat C D G) α) α
    (eq-htpy λ x → left-unit-law-comp-hom-Precat D (components-nat-trans-Precat C D F G α x))

  assoc-comp-nat-trans-Precat :
    {F G H I : functor-Precat C D}
    (α : nat-trans-Precat C D F G)(β : nat-trans-Precat C D G H)(γ : nat-trans-Precat C D H I) →
    comp-nat-trans-Precat C D F G I (comp-nat-trans-Precat C D G H I γ β) α ＝
    comp-nat-trans-Precat C D F H I γ (comp-nat-trans-Precat C D F G H β α)
  assoc-comp-nat-trans-Precat {F} {G} {H} {I} α β γ =
    eq-nat-trans-Precat F I _ _
    (eq-htpy λ x →
      assoc-comp-hom-Precat D
        (components-nat-trans-Precat C D H I γ x)
        (components-nat-trans-Precat C D G H β x)
        (components-nat-trans-Precat C D F G α x))
```
