# Structured type duality

```agda
module foundation.structured-type-duality where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.structure
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-duality
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
```

</details>

## Theorem

### Structured type duality

```agda
Slice-structure :
  {l1 l2 : Level} (l : Level) (P : UU (l1 ⊔ l) → UU l2) (B : UU l1) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
Slice-structure l P B = Σ (UU l) (λ A → hom-structure P A B)

equiv-Fib-structure :
  {l1 l2 : Level} (l : Level) (P : UU (l1 ⊔ l) → UU l2) (B : UU l1) →
  Slice-structure (l1 ⊔ l) P B ≃ fam-structure P B
equiv-Fib-structure {l1} {l3} l P B =
  ( ( inv-distributive-Π-Σ) ∘e
    ( equiv-Σ
      ( λ C → (b : B) → P (C b))
      ( equiv-Fib l B)
      ( λ f → equiv-map-Π (λ b → id-equiv)))) ∘e
  ( inv-associative-Σ
    ( UU (l1 ⊔ l))
    ( λ A → A → B)
    ( λ f → structure-map P (pr2 f)))
```

```agda
equiv-fixed-Slice-structure :
  {l : Level} (P : UU l → UU l) (X : UU l) (A : UU l) →
  ( hom-structure P X A) ≃
  ( Σ (A → Σ (UU l) (λ Z → P (Z))) ( λ Y → X ≃ (Σ A (pr1 ∘ Y))))
equiv-fixed-Slice-structure {l} P X A =
  ( ( equiv-Σ
      ( λ Y → X ≃ Σ A (pr1 ∘ Y))
      ( equiv-Fib-structure l P A)
      ( λ s →
        inv-equiv (equiv-postcomp-equiv (equiv-total-fib (pr1 (pr2 s))) X))) ∘e
    ( ( equiv-right-swap-Σ) ∘e
      ( ( inv-left-unit-law-Σ-is-contr
          ( is-contr-total-equiv X)
          ( X , id-equiv)))))
```
