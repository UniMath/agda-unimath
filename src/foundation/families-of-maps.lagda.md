# Families of maps

```agda
module foundation.families-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.families-of-equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

Given a type `A` and type families `B C : A → Type`, a **family of maps** from
`B` to `C` is an element of the type `(x : A) → B x → C x`.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1}
  (B : A → UU l2) (C : A → UU l3)
  where

  fam-map : UU (l1 ⊔ l2 ⊔ l3)
  fam-map = (x : A) → B x → C x
```

## Properties

### Families of maps are equivalent to maps of total spaces respecting the first coordinate

```agda
  equiv-fam-map-map-tot-space :
    fam-map ≃ Σ (Σ A B → Σ A C) (λ f → pr1 ~ (pr1 ∘ f))
  equiv-fam-map-map-tot-space =
    equivalence-reasoning
      fam-map
      ≃ (((x , _) : Σ A B) → C x) by equiv-ind-Σ
      ≃ (((x , _) : Σ A B) →
          Σ (Σ A (x ＝_)) λ (x' , _) → C x') by equiv-Π-equiv-family (λ (x , _) →
                                                  inv-left-unit-law-Σ-is-contr
                                                    (is-torsorial-path x)
                                                    (x , refl))
      ≃ (((x , _) : Σ A B) →
          Σ (Σ A C) λ (x' , _) → x ＝ x') by equiv-Π-equiv-family (λ (x , _) →
                                              equiv-right-swap-Σ)
      ≃ Σ (Σ A B → Σ A C)
          (λ f → pr1 ~ (pr1 ∘ f)) by distributive-Π-Σ
```

### Families of equivalences are equivalent to equivalences of total spaces respecting the first coordinate

```agda
  equiv-fam-equiv-equiv-tot-space :
    fam-equiv B C ≃ Σ (Σ A B ≃ Σ A C) (λ e → pr1 ~ (pr1 ∘ map-equiv e))
  equiv-fam-equiv-equiv-tot-space =
    equivalence-reasoning
      fam-equiv B C
      ≃ fiberwise-equiv B C by equiv-fiberwise-equiv-fam-equiv B C
      ≃ Σ (Σ (Σ A B → Σ A C)
            (λ e → pr1 ~ (pr1 ∘ e)))
          (λ (e , _) → is-equiv e) by equiv-subtype-equiv
                                        equiv-fam-map-map-tot-space
                                        (λ f → Π-Prop A (is-equiv-Prop ∘ f))
                                        (λ (e , _) → is-equiv-Prop e)
                                        (λ f →
                                          is-equiv-tot-is-fiberwise-equiv ,
                                          is-fiberwise-equiv-is-equiv-tot)
      ≃ Σ (Σ A B ≃ Σ A C)
          (λ e → pr1 ~ (pr1 ∘ map-equiv e)) by equiv-right-swap-Σ
```
