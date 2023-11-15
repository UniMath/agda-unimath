# Precategories with families

```agda
module category-theory.precategories-with-families where
```

<details><summary>Imports</summary>

```agda
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

</details>

## Idea

A **precategory with families** consists of:
* a [precategory](category-theory.precategories.md) `C`, which we think of as a category of contexts and context morphisms
* a [presheaf](category-theory.presheaf-categories.md) `Ty` on `C`, which we think of as giving the types in each context
* a [presheaf](category-theory.presheaf-categories.md) `Tm` on `∫ Ty`, which we think of as giving the terms of each type in each context
* a [functor](category-theory.functors-precategories.md) `ext` from `∫ Ty` to `C`, which we think of as context extension
such that
* for every pair of contexts `Γ` and `Δ`, and types `A` in context `Γ`, there is an equivalence between the type of context
  morphisms from `Δ` to `Γ` extended by `A`, and the type of context morphisms from `Δ` to `Γ` together with terms of `A`.

```agda
record Precategory-With-Families {l1 l2} (C : Precategory l1 l2) (l3 : Level) : UU (l1 ⊔ l2 ⊔ lsuc l3) where
  field
    Ty-F : functor-Precategory (opposite-Precategory C) (Set-Precategory l3)
    Tm-F : functor-Precategory (opposite-Precategory (element-Precategory C Ty-F)) (Set-Precategory l3)
    ext : functor-Precategory (element-Precategory C Ty-F) C
    ext-iso :
      (Δ Γ : obj-Precategory C) →
      (A : type-Set (obj-functor-Precategory (opposite-Precategory C) (Set-Precategory l3) Ty-F Γ)) →
      hom-Precategory C Δ (pr1 ext (Γ , A)) ≃
        Σ (hom-Precategory C Δ Γ) λ γ → type-Set (pr1 Tm-F (Δ , pr1 (pr2 Ty-F) γ A))

  -- Notation
  Ctx : UU l1
  Ctx = obj-Precategory C

  Sub : Ctx → Ctx → UU l2
  Sub = hom-Precategory C

  Ty : Ctx → UU l3
  Ty Γ = pr1 (pr1 Ty-F Γ)

  Tm : (Γ : Ctx)(A : Ty Γ) → UU l3
  Tm Γ A = pr1 (pr1 Tm-F (Γ , A))

  _⋆_ : (Γ : Ctx) →
      (A : type-Set (obj-functor-Precategory (opposite-Precategory C) (Set-Precategory l3) Ty-F Γ)) →
      Ctx
  Γ ⋆ A = pr1 ext (Γ , A)

  _·_ : {Δ Γ : Ctx} →
      (A : Ty Γ) →
      (γ : Sub Δ Γ) →
      Ty Δ
  A · γ = pr1 (pr2 Ty-F) γ A

  ·-comp : {Δ Δ' Γ : Ctx} →
    (A : Ty Γ) →
    (γ : Sub Δ' Γ) →
    (δ : Sub Δ Δ') →
    (A · (comp-hom-Precategory (opposite-Precategory C) δ γ)) ＝ ((A · γ) · δ)
  ·-comp A γ δ = htpy-eq (preserves-comp-functor-Precategory (opposite-Precategory C) (Set-Precategory l3) Ty-F δ γ) A

  ·-id : {Γ : Ctx} → (A : Ty Γ) → (A · id-hom-Precategory C) ＝ A
  ·-id {Γ} A = htpy-eq (preserves-id-functor-Precategory (opposite-Precategory C) (Set-Precategory l3) Ty-F Γ) A

  ext-sub : {Δ Γ : Ctx} (A : Ty Γ) (γ : Sub Δ Γ) →
    Tm Δ (A · γ) →
    Sub Δ (Γ ⋆ A)
  ext-sub {Δ} {Γ} A γ M = map-inv-equiv (ext-iso Δ Γ A) (γ , M)

  wk : {Γ : Ctx} (A : Ty Γ) → Sub (Γ ⋆ A) Γ
  wk {Γ} A = pr1 (map-equiv (ext-iso (Γ ⋆ A) Γ A) (id-hom-Precategory C))

  q : {Γ : Ctx} (A : Ty Γ) → Tm (Γ ⋆ A) (A · wk A)
  q {Γ} A = pr2 (map-equiv (ext-iso (Γ ⋆ A) Γ A) (id-hom-Precategory C))

  ⟨_,_⟩ : {Δ Γ : Ctx} (γ : Sub Δ Γ) (A : Ty Γ) → Sub (Δ ⋆ (A · γ)) (Γ ⋆ A)
  ⟨_,_⟩ {Δ} {Γ} γ A =
    ext-sub {(Δ ⋆ (A · γ))} {Γ} A
      (comp-hom-Precategory C {(Δ ⋆ (A · γ))} {Δ} {Γ} γ (wk (A · γ)))
      (tr (Tm (Δ ⋆ (A · γ))) (inv (·-comp A γ (wk (A · γ)))) (q (A · γ)))

  _[_] : {Δ Γ : Ctx} {A : Ty Γ} (M : Tm Γ A) (γ : Sub Δ Γ) → Tm Δ (A · γ)
  _[_] {Δ} {Γ} {A} M γ = pr1 (pr2 Tm-F) (γ , refl) M
```

### Π-types in a precategory with families

```agda
record Π-structure {l1 l2} (C : Precategory l1 l2) (l3 : Level) (cwf : Precategory-With-Families C l3) : UU (l1 ⊔ l2 ⊔ lsuc l3) where
  open Precategory-With-Families cwf

  field
    Π : {Γ : Ctx} (A : Ty Γ) (B : Ty (Γ ⋆ A)) → Ty Γ
    Π-iso : {Γ : Ctx} (A : Ty Γ) (B : Ty (Γ ⋆ A)) → Tm Γ (Π A B) ≃ Tm (Γ ⋆ A) B

  app : {Γ : Ctx} (A : Ty Γ) (B : Ty (Γ ⋆ A)) → Tm Γ (Π A B) → Tm (Γ ⋆ A) B
  app A B = map-equiv (Π-iso A B)

  lam : {Γ : Ctx} (A : Ty Γ) (B : Ty (Γ ⋆ A)) → Tm (Γ ⋆ A) B → Tm Γ (Π A B)
  lam A B = map-inv-equiv (Π-iso A B)

  field
    Π-sub-law : {Γ Δ : Ctx} (A : Ty Δ) (B : Ty (Δ ⋆ A)) (σ : Sub Γ Δ) →
              ((Π A B) · σ) ＝ Π (A · σ) (B · ⟨ σ , A ⟩)
    Π-iso-sub-law : {Γ Δ : Ctx} (A : Ty Δ) (B : Ty (Δ ⋆ A)) (σ : Sub Γ Δ) →
                  (t : Tm Δ (Π A B)) →
                  app (A · σ) (B · ⟨ σ , A ⟩) (tr (Tm Γ) (Π-sub-law A B σ) (t [ σ ])) ＝
                  (app A B t [ ⟨ σ , A ⟩ ])
```
