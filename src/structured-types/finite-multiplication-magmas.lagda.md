# Finite multiplication in magmas

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module structured-types.finite-multiplication-magmas
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types funext univalence truncations
open import foundation.equivalences funext
open import foundation.function-types funext
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.magmas funext univalence

open import univalent-combinatorics.counting funext univalence truncations
open import univalent-combinatorics.standard-finite-types funext univalence truncations
```

</details>

## Definition

```agda
fold-Fin-mul-Magma :
  {l : Level} (M : Magma l) → type-Magma M →
  (k : ℕ) → (Fin k → type-Magma M) → type-Magma M
fold-Fin-mul-Magma M m zero-ℕ f = m
fold-Fin-mul-Magma M m (succ-ℕ k) f =
  mul-Magma M (fold-Fin-mul-Magma M m k (f ∘ inl)) (f (inr star))

fold-count-mul-Magma' :
  {l1 l2 : Level} (M : Magma l1) → type-Magma M →
  {A : UU l2} (k : ℕ) → (Fin k ≃ A) → (A → type-Magma M) → type-Magma M
fold-count-mul-Magma' M m k e f = fold-Fin-mul-Magma M m k (f ∘ map-equiv e)

fold-count-mul-Magma :
  {l1 l2 : Level} (M : Magma l1) → type-Magma M →
  {A : UU l2} → count A → (A → type-Magma M) → type-Magma M
fold-count-mul-Magma M m e f =
  fold-Fin-mul-Magma M m (number-of-elements-count e) (f ∘ map-equiv-count e)
```
