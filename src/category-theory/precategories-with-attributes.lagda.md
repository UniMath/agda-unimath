---
title: Precategories with attributes
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module category-theory.precategories-with-attributes where

open import foundation.action-on-identifications-functions
open import foundation.category-of-sets
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import category-theory.functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.opposite-precategories
open import category-theory.precategories
open import category-theory.precategory-of-elements-of-a-presheaf
open import category-theory.pullbacks-in-precategories
```

## Idea

A category with attributes consists of:
* a category `C`, which we think of as a category of contexts and context morphisms
* a presheaf `Ty` on `C`, which we think of as giving the types in each context
* a functor `ext` from `∫ Ty` to `C`, which we think of as context extension
* a natural transformation `p` from `ext` to the projection from `∫ Ty` to `C`
such that
* the components of `p` are pullback squares

This is a reformulation of Definition 1, slide 24 of https://staff.math.su.se/palmgren/ErikP_Variants_CWF.pdf

```agda
record CwA {i j} (C : Precategory i j) (k : Level) : UU (i ⊔ j ⊔ lsuc k) where
  field
    Ty-F : functor-Precategory (opposite-Precategory C) (Set-Precategory k)
    ext : functor-Precategory (element-Precategory C Ty-F) C
    p : natural-transformation-Precategory (element-Precategory C Ty-F) C ext (proj₁-functor-element-Precategory C Ty-F)
    is-pullback-p : (x y : obj-Precategory (element-Precategory C Ty-F)) (f : hom-Precategory (element-Precategory C Ty-F) x y) →
      is-pullback-Precategory C _ _ _ _ _ _ _ _
        (naturality-natural-transformation-Precategory (element-Precategory C Ty-F) C ext (proj₁-functor-element-Precategory C Ty-F) p f)

  -- Notation
  Ctx : UU i
  Ctx = obj-Precategory C

  Sub : Ctx → Ctx → UU j
  Sub = hom-Precategory C

  Ty : Ctx → UU k
  Ty Γ = pr1 (pr1 Ty-F Γ)

  _⋆_ : (Γ : Ctx)
      → (A : type-Set (obj-functor-Precategory (opposite-Precategory C) (Set-Precategory k) Ty-F Γ))
      → Ctx
  Γ ⋆ A = pr1 ext (Γ , A)

  _·_ : {Γ Δ : Ctx}
      → (A : Ty Δ)
      → (σ : Sub Γ Δ)
      → Ty Γ
  A · σ = pr1 (pr2 Ty-F) σ A

  ⟨_,_⟩ : {Γ Δ : Ctx} (σ : Sub Γ Δ) (A : Ty Δ)
        → Sub (Γ ⋆ (A · σ)) (Δ ⋆ A)
  ⟨ σ , A ⟩ = pr1 (pr2 ext) (σ , refl)
```

The terms are defined as sections to `ext`.

```agda
  module _ (Γ : Ctx)
    (A : type-Set (obj-functor-Precategory (opposite-Precategory C) (Set-Precategory k) Ty-F Γ)) where

    Tm : UU j
    Tm = Σ (Sub Γ (Γ ⋆ A)) λ t →
           comp-hom-Precategory C (pr1 p (Γ , A)) t ＝ id-hom-Precategory C

    is-set-Tm : is-set Tm
    is-set-Tm =
      is-set-type-subtype
        (λ t → Id-Prop (hom-set-Precategory C Γ Γ) (comp-hom-Precategory C (pr1 p (Γ , A)) t) (id-hom-Precategory C))
        (is-set-hom-Precategory C Γ (Γ ⋆ A))

    Tm-Set : Set j
    pr1 Tm-Set = Tm
    pr2 Tm-Set = is-set-Tm

  _[_] : {Γ Δ : Ctx}
       → {A : Ty Δ}
       → (t : Tm Δ A)
       → (σ : Sub Γ Δ)
       → Tm Γ (A · σ)
  _[_] {Γ} {Δ} {A} (s , eq) σ = (pr1 gap-map , pr1 (pr2 gap-map))
    where
    sq : comp-hom-Precategory C σ (id-hom-Precategory C)
       ＝ comp-hom-Precategory C (pr1 p (Δ , A)) (comp-hom-Precategory C s σ)
    sq =
      equational-reasoning
        comp-hom-Precategory C σ (id-hom-Precategory C)
          ＝ σ                                       by right-unit-law-comp-hom-Precategory C σ
          ＝ comp-hom-Precategory C (id-hom-Precategory C) σ   by inv (left-unit-law-comp-hom-Precategory C σ)
          ＝ comp-hom-Precategory C
               (comp-hom-Precategory C (pr1 p (Δ , A)) s)
               σ                                     by ap (λ k → comp-hom-Precategory C k σ) (inv eq)
          ＝ comp-hom-Precategory C
               (pr1 p (Δ , A))
               (comp-hom-Precategory C s σ)               by associative-comp-hom-Precategory C _ _ _

    gap-map : Σ (Sub Γ (Γ ⋆ (A · σ))) λ g
            → (comp-hom-Precategory C (pr1 p (Γ , (A · σ))) g ＝ id-hom-Precategory C)
            × (comp-hom-Precategory C (pr1 (pr2 ext) (σ , refl)) g ＝ comp-hom-Precategory C s σ)
    gap-map =
      pr1 (is-pullback-p (Γ , (A · σ)) (Δ , A) (σ , refl) Γ (id-hom-Precategory C)
             (comp-hom-Precategory C s σ) sq)
```

### Π-types

```agda
record Π-structure {i j} (C : Precategory i j) (k : Level) (cwa : CwA C k) : UU (i ⊔ j ⊔ lsuc k) where
  open CwA cwa

  field
    Π : {Γ : Ctx} (A : Ty Γ) (B : Ty (Γ ⋆ A)) → Ty Γ
    Π-iso : {Γ : Ctx} (A : Ty Γ) (B : Ty (Γ ⋆ A))
          → Tm Γ (Π A B) ≃ Tm (Γ ⋆ A) B

  app : {Γ : Ctx} (A : Ty Γ) (B : Ty (Γ ⋆ A))
      → Tm Γ (Π A B) → Tm (Γ ⋆ A) B
  app A B = map-equiv (Π-iso A B)

  lam : {Γ : Ctx} (A : Ty Γ) (B : Ty (Γ ⋆ A))
      → Tm (Γ ⋆ A) B → Tm Γ (Π A B)
  lam A B = map-inv-equiv (Π-iso A B)

  field
    Π-sub-law : {Γ Δ : Ctx} (A : Ty Δ) (B : Ty (Δ ⋆ A)) (σ : Sub Γ Δ)
              → ((Π A B) · σ) ＝ Π (A · σ) (B · ⟨ σ , A ⟩)
    Π-iso-sub-law : {Γ Δ : Ctx} (A : Ty Δ) (B : Ty (Δ ⋆ A)) (σ : Sub Γ Δ)
                  → (t : Tm Δ (Π A B))
                  → app (A · σ) (B · ⟨ σ , A ⟩) (tr (Tm Γ) (Π-sub-law A B σ) (t [ σ ]))
                  ＝ (app A B t [ ⟨ σ , A ⟩ ])
```
