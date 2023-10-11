# Spectra

```agda
module synthetic-homotopy-theory.spectra where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import structured-types.pointed-equivalences
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import synthetic-homotopy-theory.prespectra

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

A **spectrum** is a [sequence](foundation.sequences.md) of
[pointed types](structured-types.pointed-types.md) `A` such that

```text
  Aₙ ≃∗ Ω Aₙ₊₁
```

for each `n : ℕ`.

## Definition

```agda
Spectrum : (l : Level) → UU (lsuc l)
Spectrum l =
  Σ (ℕ → Pointed-Type l) (λ A → (n : ℕ) → A n ≃∗ Ω (A (succ-ℕ n)))

module _
  {l : Level} (A : Spectrum l)
  where

  pointed-type-Spectrum : ℕ → Pointed-Type l
  pointed-type-Spectrum = pr1 A

  type-Spectrum : ℕ → UU l
  type-Spectrum = type-Pointed-Type ∘ pointed-type-Spectrum

  point-Spectrum : (n : ℕ) → type-Spectrum n
  point-Spectrum = point-Pointed-Type ∘ pointed-type-Spectrum

  pointed-equiv-Spectrum :
    (n : ℕ) → pointed-type-Spectrum n ≃∗ Ω (pointed-type-Spectrum (succ-ℕ n))
  pointed-equiv-Spectrum = pr2 A

  pointed-map-Spectrum :
    (n : ℕ) → pointed-type-Spectrum n →∗ Ω (pointed-type-Spectrum (succ-ℕ n))
  pointed-map-Spectrum = pointed-map-pointed-equiv ∘ pointed-equiv-Spectrum

  map-Spectrum :
    (n : ℕ) → type-Spectrum n → type-Ω (pointed-type-Spectrum (succ-ℕ n))
  map-Spectrum = map-pointed-map ∘ pointed-map-Spectrum

  prespectrum-Spectrum : Prespectrum l
  pr1 prespectrum-Spectrum = pointed-type-Spectrum
  pr2 prespectrum-Spectrum = pointed-map-Spectrum
```
