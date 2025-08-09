# Disjunctions

```agda
module univalent-combinatorics.disjunction where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import foundation.disjunction
open import foundation.coproduct-types
open import foundation.existential-quantification
open import foundation.function-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.finite-types
open import foundation.universe-levels
open import foundation.propositions
open import foundation.universal-quantification
open import logic.functoriality-existential-quantification
```

</details>

## Properties

### Given a function `(i : Fin n) → A i ∨ B i`, we have `∀' (Fin n) A ∨ ∃ (Fin n) B`

```agda
Π-disjunction-Fin :
  {l1 l2 : Level} → (n : ℕ) (A : Fin n → Prop l1) (B : Fin n → Prop l2) →
  ((i : Fin n) → type-disjunction-Prop (A i) (B i)) →
  type-disjunction-Prop (Π-Prop (Fin n) A) (∃ (Fin n) B)
Π-disjunction-Fin zero-ℕ _ _ _ = inl-disjunction (λ ())
Π-disjunction-Fin (succ-ℕ n) A B f =
  elim-disjunction
    ( motive)
    ( λ Πi<n:A →
      elim-disjunction
        ( motive)
        ( λ An →
          inl-disjunction
            ( λ where
              (inl i) → Πi<n:A i
              (inr _) → An))
        ( inr-disjunction ∘ intro-exists (neg-one-Fin n))
        ( f (neg-one-Fin n)))
    ( inr-disjunction ∘ map-exists (type-Prop ∘ B) inl (λ _ Bi → Bi))
    ( Π-disjunction-Fin n (A ∘ inl) (B ∘ inl) (f ∘ inl))
  where motive = Π-Prop (Fin (succ-ℕ n)) A ∨ (∃ (Fin (succ-ℕ n)) B)
```
