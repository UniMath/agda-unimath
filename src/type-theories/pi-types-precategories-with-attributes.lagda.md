# `Π`-types in precategories with attributes

```agda
module type-theories.pi-types-precategories-with-attributes where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import type-theories.precategories-with-attributes
```

</details>

## Idea

A [precategory with attributes](type-theories.precategories-with-attributes.md)
`𝒯` is said to have
{{#concept "Π-types" Disambiguation="precategory with attributes" Agda=Π-structure-Precategory-With-Attributes}}
if it comes equipped with the following structure:

- An operation `Π : (A : Ty Γ) → Ty (ext Γ A) → Ty Γ` for every context `Γ`,
- A family of equivalences `Tm Γ (Π A B) ≃ Tm (ext Γ A) B`,

that are compatible with the substitution structure on `𝒯`.

## Definitions

### The structure of `Π`-types on a precategory with attributes

```agda
record
  Π-structure-Precategory-With-Attributes
    {l1 l2 l3 : Level} (cwa : Precategory-With-Attributes l1 l2 l3) :
    UU (l1 ⊔ l2 ⊔ l3)
  where

  open Precategory-With-Attributes cwa

  field
    Π : {Γ : Ctx} (A : Ty Γ) → Ty (ext Γ A) → Ty Γ
    iso-Π :
      {Γ : Ctx} (A : Ty Γ) (B : Ty (ext Γ A)) → Tm Γ (Π A B) ≃ Tm (ext Γ A) B

  app : {Γ : Ctx} (A : Ty Γ) (B : Ty (ext Γ A)) → Tm Γ (Π A B) → Tm (ext Γ A) B
  app A B = map-equiv (iso-Π A B)

  lam :
    {Γ : Ctx} (A : Ty Γ) (B : Ty (ext Γ A)) → Tm (ext Γ A) B → Tm Γ (Π A B)
  lam A B = map-inv-equiv (iso-Π A B)

  field
    substitution-law-Π :
      {Γ Δ : Ctx} (A : Ty Δ) (B : Ty (ext Δ A)) (σ : Sub Γ Δ) →
      (Π A B) · σ ＝ Π (A · σ) (B · ⟨ σ , A ⟩)
    substitution-law-iso-Π :
      {Γ Δ : Ctx} (A : Ty Δ) (B : Ty (ext Δ A)) (σ : Sub Γ Δ) →
      (t : Tm Δ (Π A B)) →
      app
        ( A · σ)
        ( B · ⟨ σ , A ⟩)
        ( tr (Tm Γ) (substitution-law-Π A B σ) (t [ σ ])) ＝
      app A B t [ ⟨ σ , A ⟩ ]
```
