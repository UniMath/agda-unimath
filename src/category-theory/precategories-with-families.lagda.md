---
title: Precategories with families
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module category-theory.precategories-with-families where

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equational-reasoning
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import category-theory.functors-precategories
open import category-theory.natural-transformations-precategories
open import category-theory.opposite-precategory
open import category-theory.precategories
open import category-theory.precategory-of-elements-of-a-presheaf
open import category-theory.pullbacks-precategories
```
TODO

```agda
record CwF {i j} (C : Precat i j) (k : Level) : UU (i ⊔ j ⊔ lsuc k) where
  field
    Ty-F : functor-Precat (op C) (Set-Precat k)
    Tm-F : functor-Precat (op (element-Precat C Ty-F)) (Set-Precat k)

    ext : functor-Precat (element-Precat C Ty-F) C

    -- Maps into Γ.A ~ maps into Γ and terms of A.
    ext-iso :
      (Δ Γ : obj-Precat C)
      → (A : type-Set (obj-functor-Precat (op C) (Set-Precat k) Ty-F Γ))
      → type-hom-Precat C Δ (pr1 ext (Γ , A))
        ≃ Σ (type-hom-Precat C Δ Γ) λ γ → type-Set (pr1 Tm-F (Δ , pr1 (pr2 Ty-F) γ A))

  -- Notation
  Ctx : UU i
  Ctx = obj-Precat C

  Sub : Ctx → Ctx → UU j
  Sub = type-hom-Precat C

  Ty : Ctx → UU k
  Ty Γ = pr1 (pr1 Ty-F Γ)

  Tm : (Γ : Ctx)(A : Ty Γ) → UU k
  Tm Γ A = pr1 (pr1 Tm-F (Γ , A))

  _⋆_ : (Γ : Ctx)
      → (A : type-Set (obj-functor-Precat (op C) (Set-Precat k) Ty-F Γ))
      → Ctx
  Γ ⋆ A = pr1 ext (Γ , A)

  _·_ : {Δ Γ : Ctx}
      → (A : Ty Γ)
      → (γ : Sub Δ Γ)
      → Ty Δ
  A · γ = pr1 (pr2 Ty-F) γ A

  ·-comp : {Δ Δ' Γ : Ctx}
      → (A : Ty Γ)
      → (γ : Sub Δ' Γ)
      → (δ : Sub Δ Δ')
      → (A · (comp-hom-Precat (op C) δ γ)) ＝ ((A · γ) · δ)
  ·-comp A γ δ = htpy-eq (respects-comp-functor-Precat (op C) (Set-Precat k) Ty-F δ γ) A

  ·-id : {Γ : Ctx} → (A : Ty Γ) → (A · id-hom-Precat C) ＝ A
  ·-id {Γ} A = htpy-eq (respects-id-functor-Precat (op C) (Set-Precat k) Ty-F Γ) A

  ext-sub : {Δ Γ : Ctx} (A : Ty Γ) (γ : Sub Δ Γ)
    → Tm Δ (A · γ)
    → Sub Δ (Γ ⋆ A)
  ext-sub {Δ} {Γ} A γ M = map-inv-equiv (ext-iso Δ Γ A) (γ , M)

  wk : {Γ : Ctx} (A : Ty Γ) → Sub (Γ ⋆ A) Γ
  wk {Γ} A = pr1 (map-equiv (ext-iso (Γ ⋆ A) Γ A) (id-hom-Precat C))

  q : {Γ : Ctx} (A : Ty Γ) → Tm (Γ ⋆ A) (A · wk A)
  q {Γ} A = pr2 (map-equiv (ext-iso (Γ ⋆ A) Γ A) (id-hom-Precat C))

  ⟨_,_⟩ : {Δ Γ : Ctx} (γ : Sub Δ Γ) (A : Ty Γ) → Sub (Δ ⋆ (A · γ)) (Γ ⋆ A)
  ⟨_,_⟩ {Δ} {Γ} γ A =
    ext-sub {(Δ ⋆ (A · γ))} {Γ} A
      (comp-hom-Precat C {(Δ ⋆ (A · γ))} {Δ} {Γ} γ (wk (A · γ)))
      (tr (Tm (Δ ⋆ (A · γ))) (inv (·-comp A γ (wk (A · γ)))) (q (A · γ)))

  _[_] : {Δ Γ : Ctx} {A : Ty Γ} (M : Tm Γ A) (γ : Sub Δ Γ) → Tm Δ (A · γ)
  _[_] {Δ} {Γ} {A} M γ = pr1 (pr2 Tm-F) (γ , refl) M
```

-- ### Π-types

```agda
record Π-structure {i j} (C : Precat i j) (k : Level) (cwf : CwF C k) : UU (i ⊔ j ⊔ lsuc k) where
  open CwF cwf

  field
    Π : {Γ : Ctx} (A : Ty Γ) (B : Ty (Γ ⋆ A)) → Ty Γ
    Π-iso : {Γ : Ctx} (A : Ty Γ) (B : Ty (Γ ⋆ A)) → Tm Γ (Π A B) ≃ Tm (Γ ⋆ A) B

  app : {Γ : Ctx} (A : Ty Γ) (B : Ty (Γ ⋆ A)) → Tm Γ (Π A B) → Tm (Γ ⋆ A) B
  app A B = map-equiv (Π-iso A B)

  lam : {Γ : Ctx} (A : Ty Γ) (B : Ty (Γ ⋆ A)) → Tm (Γ ⋆ A) B → Tm Γ (Π A B)
  lam A B = map-inv-equiv (Π-iso A B)

  field
    Π-sub-law : {Γ Δ : Ctx} (A : Ty Δ) (B : Ty (Δ ⋆ A)) (σ : Sub Γ Δ)
              → ((Π A B) · σ) ＝ Π (A · σ) (B · ⟨ σ , A ⟩)
    Π-iso-sub-law : {Γ Δ : Ctx} (A : Ty Δ) (B : Ty (Δ ⋆ A)) (σ : Sub Γ Δ)
                  → (t : Tm Δ (Π A B))
                  → app (A · σ) (B · ⟨ σ , A ⟩) (tr (Tm Γ) (Π-sub-law A B σ) (t [ σ ]))
                  ＝ (app A B t [ ⟨ σ , A ⟩ ])
```
