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
equiv-surjection-finite-type-family-finite-inhabited-type :
  {l : Level} (A : Finite-Type l) (B : Finite-Type l) →
  ( ( type-Finite-Type A ↠ type-Finite-Type B) ≃
    ( Σ ( type-Finite-Type B → Inhabited-Finite-Type l)
        ( λ Y →
          type-Finite-Type A ≃
          Σ (type-Finite-Type B) (λ b → type-Inhabited-Finite-Type (Y b)))))
equiv-surjection-finite-type-family-finite-inhabited-type {l} A B =
  ( equiv-Σ-equiv-base
    ( λ Y →
      type-Finite-Type A ≃
      Σ (type-Finite-Type B) (λ b → type-Inhabited-Finite-Type (Y b)))
    ( equiv-postcomp
      ( type-Finite-Type B)
      ( inv-associative-Σ ∘e equiv-tot (λ _ → commutative-product)))) ∘e
  ( equiv-fixed-Slice-structure
    ( λ x → (is-inhabited x) × (is-finite x))
    ( type-Finite-Type A)
    ( type-Finite-Type B)) ∘e
  ( equiv-tot (λ _ → inv-distributive-Π-Σ)) ∘e
  ( associative-Σ) ∘e
  ( inv-equiv-inclusion-is-full-subtype
    ( λ f →
      Π-Prop
        ( type-Finite-Type B)
        ( λ b → is-finite-Prop (fiber (pr1 f) b)))
    ( λ f →
      is-finite-fiber
        ( pr1 f)
        ( is-finite-type-Finite-Type A)
        ( is-finite-type-Finite-Type B)))

Slice-Surjection-Finite-Type :
  (l : Level) {l1 : Level} (A : Finite-Type l1) → UU (lsuc l ⊔ l1)
Slice-Surjection-Finite-Type l A =
  Σ (Finite-Type l) (λ X → type-Finite-Type X ↠ type-Finite-Type A)

equiv-Fiber-trunc-prop-Finite-Type :
  (l : Level) {l1 : Level} (A : Finite-Type l1) →
  Slice-Surjection-Finite-Type (l1 ⊔ l) A ≃
  (type-Finite-Type A → Inhabited-Finite-Type (l1 ⊔ l))
equiv-Fiber-trunc-prop-Finite-Type l {l1} A =
  ( equiv-Π-equiv-family (λ a → inv-associative-Σ)) ∘e
  ( equiv-Fiber-structure l
    ( λ X → is-finite X × is-inhabited X)
    ( type-Finite-Type A)) ∘e
  ( equiv-tot
    ( λ X →
      ( equiv-tot
        ( λ f →
          ( inv-distributive-Π-Σ) ∘e
          ( equiv-Σ-equiv-base
            ( λ _ → (x : type-Finite-Type A) → is-inhabited (fiber f x))
            ( inv-equiv-is-finite-domain-is-finite-fiber A f)))) ∘e
      ( equiv-left-swap-Σ))) ∘e
  ( associative-Σ)
```
