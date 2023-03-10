# Spectra

```agda
module synthetic-homotopy-theory.spectra where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.pointed-equivalences
open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

A spectrum is an infinite sequence of pointed types `A` such that `A n ≃* Ω (A (n+1))` for each `n : ℕ`.

## Definition

```agda
Spectrum : (l : Level) → UU (lsuc l)
Spectrum l =
  Σ (ℕ → Pointed-Type l) (λ A → (n : ℕ) → A n ≃* Ω (A (succ-ℕ n)))
```
