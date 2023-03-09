# Equivalence induction

```agda
module foundation-core.equivalence-induction where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.sections
open import foundation-core.singleton-induction
open import foundation-core.universe-levels
```

</details>

## Idea

Equivalence induction is a condition equivalent to the univalence axiom

## Properties

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  ev-id :
    { l : Level} (P : (B : UU l1) → (A ≃ B) → UU l) →
    ( (B : UU l1) (e : A ≃ B) → P B e) → P A id-equiv
  ev-id P f = f A id-equiv

  IND-EQUIV : {l : Level} (P : (B : UU l1) (e : A ≃ B) → UU l) → UU _
  IND-EQUIV P = sec (ev-id P)

  triangle-ev-id :
    { l : Level}
    ( P : (Σ (UU l1) (λ X → A ≃ X)) → UU l) →
    ( ev-pt (pair A id-equiv) P) ~
    ( ( ev-id (λ X e → P (pair X e))) ∘
      ( ev-pair {A = UU l1} {B = λ X → A ≃ X} {C = P}))
  triangle-ev-id P f = refl

  -- Theorem 17.1.1 (ii) implies (iii)

  abstract
    IND-EQUIV-is-contr-total-equiv :
      is-contr (Σ (UU l1) (λ X → A ≃ X)) →
      {l : Level} →
      (P : (Σ (UU l1) (λ X → A ≃ X)) → UU l) → IND-EQUIV (λ B e → P (pair B e))
    IND-EQUIV-is-contr-total-equiv c P =
      section-left-factor
        ( ev-id (λ X e → P (pair X e)))
        ( ev-pair)
        ( is-singleton-is-contr
          ( pair A id-equiv)
          ( pair
            ( pair A id-equiv)
            ( λ t →  ( inv (contraction c (pair A id-equiv))) ∙
                     ( contraction c t)))
          ( P))

  -- Theorem 17.1.1 (iii) implies (ii)

  abstract
    is-contr-total-equiv-IND-EQUIV :
      ( {l : Level} (P : (Σ (UU l1) (λ X → A ≃ X)) → UU l) →
        IND-EQUIV (λ B e → P (pair B e))) →
      is-contr (Σ (UU l1) (λ X → A ≃ X))
    is-contr-total-equiv-IND-EQUIV ind =
      is-contr-is-singleton
        ( Σ (UU l1) (λ X → A ≃ X))
        ( pair A id-equiv)
        ( λ P → section-comp
          ( ev-id (λ X e → P (pair X e)))
          ( ev-pair {A = UU l1} {B = λ X → A ≃ X} {C = P})
          ( pair ind-Σ refl-htpy)
          ( ind P))
```
