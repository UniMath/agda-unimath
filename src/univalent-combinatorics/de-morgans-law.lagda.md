# De Morgan's law for finite families of propositions

```agda
module univalent-combinatorics.de-morgans-law where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.decidable-dependent-pair-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.negation
open import foundation.unit-type
open import foundation.universe-levels

open import logic.de-morgan-propositions
open import logic.de-morgan-types

open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a finite family of [De Morgan types](logic.de-morgan-types.md)
`P : Fin k → De-Morgan-Type`, then the "finitary De Morgan's law"

```text
  ¬ (∀ i, P i) ⇒ ∃ i, ¬ (P i)
```

holds.

## Result

```agda
lemma-satisfies-de-morgan-Fin-is-de-morgan-family :
  {l : Level} (k : ℕ) {P : Fin (succ-ℕ k) → UU l} →
  ((x : Fin (succ-ℕ k)) → is-de-morgan (P x)) →
  ¬ ((x : Fin (succ-ℕ k)) → P x) →
  ¬ P (inr star) + ¬ ((x : Fin k) → P (inl x))
lemma-satisfies-de-morgan-Fin-is-de-morgan-family k {P} H q =
  rec-coproduct
    ( inl)
    ( λ z → inr (λ y → z (λ y' → q (ind-coproduct P y (λ _ → y')))))
    ( H (inr star))

satisfies-de-morgan-Fin-is-de-morgan-family :
  {l : Level} (k : ℕ) {P : Fin k → UU l} →
  ((x : Fin k) → is-de-morgan (P x)) →
  ¬ ((x : Fin k) → P x) →
  Σ (Fin k) (¬_ ∘ P)
satisfies-de-morgan-Fin-is-de-morgan-family zero-ℕ {P} H q =
  q (λ ()) , (λ x → q (λ ()))
satisfies-de-morgan-Fin-is-de-morgan-family (succ-ℕ k) {P} H q =
  rec-coproduct
    ( inr star ,_)
    ( λ q' →
      map-Σ-map-base inl
        ( ¬_ ∘ P)
        ( satisfies-de-morgan-Fin-is-de-morgan-family k (H ∘ inl) q'))
    ( lemma-satisfies-de-morgan-Fin-is-de-morgan-family k H q)
```

```agda
module _
  {l : Level} {k : ℕ} (P : Fin k → De-Morgan-Type l)
  where

  satisfies-de-morgan-family-Fin :
    ¬ ((x : Fin k) → type-De-Morgan-Type (P x)) →
    Σ (Fin k) (¬_ ∘ type-De-Morgan-Type ∘ P)
  satisfies-de-morgan-family-Fin =
    satisfies-de-morgan-Fin-is-de-morgan-family k
      ( is-de-morgan-type-De-Morgan-Type ∘ P)
```

## Comment

It is likely that this "finitary De Morgan's law" can be generalized to families
of De Morgan types indexed by _searchable types_ in the sense of Escardó
{{#cite Esc08}}.

## References

{{#bibliography}}
