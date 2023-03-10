# Decidability of dependent pair types

```agda
module univalent-combinatorics.decidable-dependent-pair-types where
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
open import foundation.functions
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We describe conditions under which dependent sums are decidable. Note that it is _not_ the case for a family `B` of decidable types over a finite type `A`, that the dependent pair type `Σ A B` is decidable.

## Properties

### The Σ-type of any family of decidable types over `Fin k` is decidable

```agda
is-decidable-Σ-Fin :
  {l : Level} (k : ℕ) {P : Fin k → UU l} →
  ((x : Fin k) → is-decidable (P x)) → is-decidable (Σ (Fin k) P)
is-decidable-Σ-Fin zero-ℕ {P} d = inr pr1
is-decidable-Σ-Fin (succ-ℕ k) {P} d with d (inr star)
... | inl p = inl (pair (inr star) p)
... | inr f =
  is-decidable-iff
    ( λ t → pair (inl (pr1 t)) (pr2 t))
    ( g)
    ( is-decidable-Σ-Fin k {P ∘ inl} (λ x → d (inl x)))
  where
  g : Σ (Fin (succ-ℕ k)) P → Σ (Fin k) (P ∘ inl)
  g (pair (inl x) p) = pair x p
  g (pair (inr star) p) = ex-falso (f p)
```

### The Σ-type of any family of decidable types over a type equipped with count is decidable

```agda
is-decidable-Σ-count :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count A →
  ((x : A) → is-decidable (B x)) → is-decidable (Σ A B)
is-decidable-Σ-count e d =
  is-decidable-Σ-equiv
    ( equiv-count e)
    ( λ x → id-equiv)
    ( is-decidable-Σ-Fin
      ( number-of-elements-count e)
      ( λ x → d (map-equiv-count e x)))
```
