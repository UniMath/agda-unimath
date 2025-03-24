# Subtype duality

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.subtype-duality
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.inhabited-types funext univalence truncations
open import foundation.propositional-maps funext
open import foundation.structured-type-duality funext univalence truncations
open import foundation.surjective-maps funext univalence truncations
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

equiv-Fiber-Prop :
  (l : Level) {l1 : Level} (A : UU l1) →
  Slice-emb (l1 ⊔ l) A ≃ (A → Prop (l1 ⊔ l))
equiv-Fiber-Prop l A =
  ( equiv-Fiber-structure l is-prop A) ∘e
  ( equiv-tot (λ X → equiv-tot equiv-is-prop-map-is-emb))

Slice-surjection : (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
Slice-surjection l A = Σ (UU l) (λ X → X ↠ A)

equiv-Fiber-trunc-Prop :
  (l : Level) {l1 : Level} (A : UU l1) →
  Slice-surjection (l1 ⊔ l) A ≃ (A → Inhabited-Type (l1 ⊔ l))
equiv-Fiber-trunc-Prop l A =
  ( equiv-Fiber-structure l is-inhabited A)
```
