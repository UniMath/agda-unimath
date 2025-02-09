# Type duality of finite types

```agda
module univalent-combinatorics.type-duality where

open import foundation.type-duality public
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.full-subtypes
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-function-types
open import foundation.inhabited-types
open import foundation.postcomposition-functions
open import foundation.propositions
open import foundation.structure
open import foundation.structured-type-duality
open import foundation.surjective-maps
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import univalent-combinatorics.fibers-of-maps
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
```

</details>

## Properties

### Subtype duality

```agda
equiv-surjection-𝔽-family-finite-inhabited-type :
  {l : Level} (A : Finite-Type l) (B : Finite-Type l) →
  ( (type-Finite-Type A ↠ type-Finite-Type B) ≃
    ( Σ ( (type-Finite-Type B) → Inhabited-Finite-Type l)
        ( λ Y → (type-Finite-Type A) ≃ Σ (type-Finite-Type B) (λ b → type-Inhabited-Finite-Type (Y b)))))
equiv-surjection-𝔽-family-finite-inhabited-type {l} A B =
  ( ( equiv-Σ
      ( λ Y → type-Finite-Type A ≃ Σ (type-Finite-Type B) (λ b → type-Inhabited-Finite-Type (Y b)))
      ( equiv-postcomp
        ( type-Finite-Type B)
        ( inv-associative-Σ ( UU l) is-finite ( λ X → is-inhabited (pr1 X)) ∘e
          equiv-Σ
            ( λ z → is-finite z × is-inhabited z)
            ( id-equiv)
            ( λ _ → commutative-product)))
      ( λ b → id-equiv)) ∘e
    ( ( equiv-fixed-Slice-structure
        ( λ x → (is-inhabited x) × (is-finite x))
        ( type-Finite-Type A)
        ( type-Finite-Type B)) ∘e
      ( ( equiv-Σ
          ( structure-map (λ x → is-inhabited x × is-finite x))
          ( id-equiv)
          ( λ _ → inv-equiv distributive-Π-Σ)) ∘e
        ( ( associative-Σ
            ( type-Finite-Type A → type-Finite-Type B)
            ( structure-map is-inhabited)
            ( _)) ∘e
          ( ( inv-equiv
              ( equiv-inclusion-is-full-subtype
                ( λ f →
                  Π-Prop (type-Finite-Type B) (λ b → is-finite-Prop (fiber (pr1 f) b)))
                ( λ f →
                  is-finite-fiber
                    ( pr1 f)
                    ( is-finite-type-Finite-Type A)
                    ( is-finite-type-Finite-Type B)))))))))

Slice-Surjection-Finite-Type : (l : Level) {l1 : Level} (A : Finite-Type l1) → UU (lsuc l ⊔ l1)
Slice-Surjection-Finite-Type l A = Σ (Finite-Type l) (λ X → (type-Finite-Type X) ↠ type-Finite-Type A)

equiv-Fiber-trunc-prop-Finite-Type :
  (l : Level) {l1 : Level} (A : Finite-Type l1) →
  Slice-Surjection-Finite-Type (l1 ⊔ l) A ≃ (type-Finite-Type A → Inhabited-Finite-Type (l1 ⊔ l))
equiv-Fiber-trunc-prop-Finite-Type l {l1} A =
  ( ( equiv-Π
      ( λ _ → Inhabited-Finite-Type _)
      ( id-equiv)
      ( λ a → inv-associative-Σ _ _ _) ∘e
      ( ( equiv-Fiber-structure
          ( l)
          ( λ X → is-finite X × is-inhabited X) (type-Finite-Type A)))) ∘e
    ( ( equiv-Σ
        ( _)
        ( id-equiv)
        ( λ X →
          ( equiv-Σ
            ( _)
            ( id-equiv)
            ( λ f →
              ( inv-equiv distributive-Π-Σ) ∘e
              ( equiv-Σ-equiv-base
                ( _)
                ( inv-equiv
                  ( equiv-is-finite-domain-is-finite-fiber A f)))))) ∘e
      ( ( equiv-Σ
          ( _)
          ( id-equiv)
          ( λ _ → equiv-left-swap-Σ)) ∘e
        ( associative-Σ (UU (l ⊔ l1)) (is-finite) _)))))
```
