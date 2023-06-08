# Subtype duality

```agda
module foundation.subtype-duality where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.propositional-maps
open import foundation.structured-type-duality
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.propositions
```

</details>

## Theorem

### Subtype duality

```agda
Slice-emb : (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
Slice-emb l A = Σ (UU l) (λ X → X ↪ A)

equiv-Fib-Prop :
  (l : Level) {l1 : Level} (A : UU l1) →
  Slice-emb (l1 ⊔ l) A ≃ (A → Prop (l1 ⊔ l))
equiv-Fib-Prop l A =
  ( equiv-Fib-structure l is-prop A) ∘e
  ( equiv-tot (λ X → equiv-tot equiv-is-prop-map-is-emb))

Slice-surjection : (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
Slice-surjection l A = Σ (UU l) (λ X → X ↠ A)

equiv-Fib-trunc-Prop :
  (l : Level) {l1 : Level} (A : UU l1) →
  Slice-surjection (l1 ⊔ l) A ≃ (A → Inhabited-Type (l1 ⊔ l))
equiv-Fib-trunc-Prop l A =
  ( equiv-Fib-structure l is-inhabited A)
```
