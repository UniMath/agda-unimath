# Equivalence extensionality

```agda
module foundation.equivalence-extensionality where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionality
open import foundation.subtype-identity-principle
open import foundation.type-theoretic-principle-of-choice

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.functions
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.fundamental-theorem-of-identity-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.universe-levels
```

</details>

## Characterizing the identity type of equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  htpy-equiv : A ≃ B → A ≃ B → UU (l1 ⊔ l2)
  htpy-equiv e e' = (map-equiv e) ~ (map-equiv e')

  extensionality-equiv : (f g : A ≃ B) → (f ＝ g) ≃ htpy-equiv f g
  extensionality-equiv f =
    extensionality-type-subtype
      ( is-equiv-Prop)
      ( pr2 f)
      ( refl-htpy' (pr1 f))
      ( λ g → equiv-funext)
    where
      is-equiv-Prop : (f : A → B) → Prop (l1 ⊔ l2)
      pr1 (is-equiv-Prop f) = is-equiv f
      pr2 (is-equiv-Prop f) H =
        is-prop-is-contr
          ( is-contr-prod
            ( is-contr-equiv'
              ( (b : B) → fib f b)
              ( distributive-Π-Σ)
              ( is-contr-Π (is-contr-map-is-equiv H)))
            ( is-contr-is-equiv'
              ( Σ (B → A) (λ h → (h ∘ f) ＝ id))
              ( tot (λ h → htpy-eq))
              ( is-equiv-tot-is-fiberwise-equiv
                ( λ h → funext (h ∘ f) id))
              ( is-contr-map-is-equiv
                (( is-equiv-precomp-Π-is-equiv f H) (λ y → A))
                ( id))))
          ( H)

  abstract
    is-contr-total-htpy-equiv :
      (e : A ≃ B) → is-contr (Σ (A ≃ B) (htpy-equiv e))
    is-contr-total-htpy-equiv e =
      fundamental-theorem-id'
        ( λ f → map-equiv (extensionality-equiv e f))
        ( λ f → is-equiv-map-equiv (extensionality-equiv e f))

  refl-htpy-equiv : (e : A ≃ B) → htpy-equiv e e
  refl-htpy-equiv e = refl-htpy

  eq-htpy-equiv : {e e' : A ≃ B} → (htpy-equiv e e') → e ＝ e'
  eq-htpy-equiv {e = e} {e'} = map-inv-equiv (extensionality-equiv e e')

  htpy-eq-equiv : {e e' : A ≃ B} → e ＝ e' → htpy-equiv e e'
  htpy-eq-equiv {e} {e'} = map-equiv (extensionality-equiv e e')

  htpy-eq-map-equiv :
    {e e' : A ≃ B} → (map-equiv e) ＝ (map-equiv e') → htpy-equiv e e'
  htpy-eq-map-equiv = htpy-eq
```
