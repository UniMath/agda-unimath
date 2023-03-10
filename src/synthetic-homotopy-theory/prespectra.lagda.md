# Prespectra

```agda
module synthetic-homotopy-theory.prespectra where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

A prespectrum is a sequence of pointed types `A n` equipped with pointed maps `ε : A n →* Ω (A (n+1))`.

## Definition

```agda
Prespectrum : (l : Level) → UU (lsuc l)
Prespectrum l =
  Σ (ℕ → Pointed-Type l) (λ A → (n : ℕ) → A n →* Ω (A (succ-ℕ n)))
```
