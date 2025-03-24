# De Morgan's law for finite families of propositions

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module univalent-combinatorics.de-morgans-law
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types funext univalence truncations
open import foundation.decidable-dependent-pair-types funext univalence truncations
open import foundation.decidable-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.empty-types funext univalence truncations
open import foundation.equivalences funext
open import foundation.existential-quantification funext univalence truncations
open import foundation.function-types funext
open import foundation.functoriality-dependent-pair-types funext
open import foundation.negation funext
open import foundation.unit-type
open import foundation.universe-levels

open import logic.de-morgan-propositions funext univalence truncations
open import logic.de-morgan-types funext univalence truncations

open import univalent-combinatorics.counting funext univalence truncations
open import univalent-combinatorics.standard-finite-types funext univalence truncations
```

</details>

## Idea

Given a [finite](univalent-combinatorics.finite-types.md) family of
[De Morgan types](logic.de-morgan-types.md) `P : Fin k → De-Morgan-Type`, then
the _finitary De Morgan's law_

```text
  ¬ (∀ i, P i) ⇒ ∃ i, ¬ (P i)
```

holds.

## Result

```agda
cases-decide-de-morgans-law-family-Fin-is-de-morgan-family :
  {l : Level} (k : ℕ) {P : Fin (succ-ℕ k) → UU l} →
  ((x : Fin (succ-ℕ k)) → is-de-morgan (P x)) →
  ¬ ((x : Fin (succ-ℕ k)) → P x) →
  ¬ P (inr star) + ¬ ((x : Fin k) → P (inl x))
cases-decide-de-morgans-law-family-Fin-is-de-morgan-family k {P} H q =
  rec-coproduct
    ( inl)
    ( λ z → inr (λ y → z (λ y' → q (ind-coproduct P y (λ _ → y')))))
    ( H (inr star))

decide-de-morgans-law-family-Fin-is-de-morgan-family :
  {l : Level} (k : ℕ) {P : Fin k → UU l} →
  ((x : Fin k) → is-de-morgan (P x)) →
  ¬ ((x : Fin k) → P x) →
  Σ (Fin k) (¬_ ∘ P)
decide-de-morgans-law-family-Fin-is-de-morgan-family zero-ℕ {P} H q =
  q (λ ()) , (λ x → q (λ ()))
decide-de-morgans-law-family-Fin-is-de-morgan-family (succ-ℕ k) {P} H q =
  rec-coproduct
    ( inr star ,_)
    ( λ q' →
      map-Σ-map-base inl
        ( ¬_ ∘ P)
        ( decide-de-morgans-law-family-Fin-is-de-morgan-family k (H ∘ inl) q'))
    ( cases-decide-de-morgans-law-family-Fin-is-de-morgan-family k H q)
```

```agda
module _
  {l : Level} {k : ℕ} (P : Fin k → De-Morgan-Type l)
  where

  decide-de-morgans-law-family-family-Fin :
    ¬ ((x : Fin k) → type-De-Morgan-Type (P x)) →
    Σ (Fin k) (¬_ ∘ type-De-Morgan-Type ∘ P)
  decide-de-morgans-law-family-family-Fin =
    decide-de-morgans-law-family-Fin-is-de-morgan-family k
      ( is-de-morgan-type-De-Morgan-Type ∘ P)
```

## Comment

It is likely that this finitary De Morgan's law can be generalized to families
of De Morgan types indexed by _searchable types_ in the sense of Escardó
{{#cite Esc08}}.

## References

{{#bibliography}}
