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
  {l : Level} (A : 𝔽 l) (B : 𝔽 l) →
  ( (type-𝔽 A ↠ type-𝔽 B) ≃
    ( Σ ( (type-𝔽 B) → Inhabited-𝔽 l)
        ( λ Y → (type-𝔽 A) ≃ Σ (type-𝔽 B) (λ b → type-Inhabited-𝔽 (Y b)))))
equiv-surjection-𝔽-family-finite-inhabited-type {l} A B =
  ( ( equiv-Σ
      ( λ Y → type-𝔽 A ≃ Σ (type-𝔽 B) (λ b → type-Inhabited-𝔽 (Y b)))
      ( equiv-postcomp
        ( type-𝔽 B)
        ( inv-associative-Σ ( UU l) is-finite ( λ X → is-inhabited (pr1 X)) ∘e
          equiv-Σ
            ( λ z → is-finite z × is-inhabited z)
            ( id-equiv)
            ( λ _ → commutative-product)))
      ( λ b → id-equiv)) ∘e
    ( ( equiv-fixed-Slice-structure
        ( λ x → (is-inhabited x) × (is-finite x))
        ( type-𝔽 A)
        ( type-𝔽 B)) ∘e
      ( ( equiv-Σ
          ( structure-map (λ x → is-inhabited x × is-finite x))
          ( id-equiv)
          ( λ _ → inv-equiv distributive-Π-Σ)) ∘e
        ( ( associative-Σ
            ( type-𝔽 A → type-𝔽 B)
            ( structure-map is-inhabited)
            ( _)) ∘e
          ( ( inv-equiv
              ( equiv-inclusion-is-full-subtype
                ( λ f →
                  Π-Prop (type-𝔽 B) (λ b → is-finite-Prop (fiber (pr1 f) b)))
                ( λ f →
                  is-finite-fiber
                    ( pr1 f)
                    ( is-finite-type-𝔽 A)
                    ( is-finite-type-𝔽 B)))))))))

Slice-Surjection-𝔽 : (l : Level) {l1 : Level} (A : 𝔽 l1) → UU (lsuc l ⊔ l1)
Slice-Surjection-𝔽 l A = Σ (𝔽 l) (λ X → (type-𝔽 X) ↠ type-𝔽 A)

equiv-Fiber-trunc-Prop-𝔽 :
  (l : Level) {l1 : Level} (A : 𝔽 l1) →
  Slice-Surjection-𝔽 (l1 ⊔ l) A ≃ (type-𝔽 A → Inhabited-𝔽 (l1 ⊔ l))
equiv-Fiber-trunc-Prop-𝔽 l {l1} A =
  ( ( equiv-Π
      ( λ _ → Inhabited-𝔽 _)
      ( id-equiv)
      ( λ a → inv-associative-Σ _ _ _) ∘e
      ( ( equiv-Fiber-structure
          ( l)
          ( λ X → is-finite X × is-inhabited X) (type-𝔽 A)))) ∘e
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
