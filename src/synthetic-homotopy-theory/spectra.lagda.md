# Spectra

```agda
module synthetic-homotopy-theory.spectra where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import structured-types.pointed-equivalences
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.prespectra
open import synthetic-homotopy-theory.suspensions-of-pointed-types
open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

A **spectrum** is a [sequence](lists.sequences.md) of
[pointed types](structured-types.pointed-types.md) `A` equipped with an
equivalence

```text
  Aₙ ≃∗ ΩAₙ₊₁
```

for each `n : ℕ`.

## Definition

### The predicate on prespectra of being a spectrum

```agda
is-spectrum-Prop : {l : Level} → Prespectrum l → Prop l
is-spectrum-Prop A =
  Π-Prop ℕ
    ( λ n →
      is-pointed-equiv-Prop (pointed-adjoint-structure-map-Prespectrum A n))

is-spectrum : {l : Level} → Prespectrum l → UU l
is-spectrum = type-Prop ∘ is-spectrum-Prop

is-prop-is-spectrum : {l : Level} (A : Prespectrum l) → is-prop (is-spectrum A)
is-prop-is-spectrum = is-prop-type-Prop ∘ is-spectrum-Prop
```

### The type of spectra

```agda
Spectrum : (l : Level) → UU (lsuc l)
Spectrum l = Σ (Prespectrum l) (is-spectrum)

module _
  {l : Level} (A : Spectrum l)
  where

  prespectrum-Spectrum : Prespectrum l
  prespectrum-Spectrum = pr1 A

  pointed-type-Spectrum : ℕ → Pointed-Type l
  pointed-type-Spectrum = pointed-type-Prespectrum prespectrum-Spectrum

  type-Spectrum : ℕ → UU l
  type-Spectrum = type-Prespectrum prespectrum-Spectrum

  point-Spectrum : (n : ℕ) → type-Spectrum n
  point-Spectrum = point-Prespectrum prespectrum-Spectrum

  pointed-adjoint-structure-map-Spectrum :
    (n : ℕ) → pointed-type-Spectrum n →∗ Ω (pointed-type-Spectrum (succ-ℕ n))
  pointed-adjoint-structure-map-Spectrum =
    pointed-adjoint-structure-map-Prespectrum prespectrum-Spectrum

  adjoint-structure-map-Spectrum :
    (n : ℕ) → type-Spectrum n → type-Ω (pointed-type-Spectrum (succ-ℕ n))
  adjoint-structure-map-Spectrum =
    adjoint-structure-map-Prespectrum prespectrum-Spectrum

  preserves-point-adjoint-structure-map-Spectrum :
    (n : ℕ) →
    adjoint-structure-map-Prespectrum (pr1 A) n (point-Prespectrum (pr1 A) n) ＝
    refl-Ω (pointed-type-Prespectrum (pr1 A) (succ-ℕ n))
  preserves-point-adjoint-structure-map-Spectrum =
    preserves-point-adjoint-structure-map-Prespectrum prespectrum-Spectrum

  is-equiv-pointed-adjoint-structure-map-Spectrum :
    (n : ℕ) → is-pointed-equiv (pointed-adjoint-structure-map-Spectrum n)
  is-equiv-pointed-adjoint-structure-map-Spectrum = pr2 A

  structure-equiv-Spectrum :
    (n : ℕ) → type-Spectrum n ≃ type-Ω (pointed-type-Spectrum (succ-ℕ n))
  pr1 (structure-equiv-Spectrum n) = adjoint-structure-map-Spectrum n
  pr2 (structure-equiv-Spectrum n) =
    is-equiv-pointed-adjoint-structure-map-Spectrum n

  pointed-structure-equiv-Spectrum :
    (n : ℕ) → pointed-type-Spectrum n ≃∗ Ω (pointed-type-Spectrum (succ-ℕ n))
  pr1 (pointed-structure-equiv-Spectrum n) = structure-equiv-Spectrum n
  pr2 (pointed-structure-equiv-Spectrum n) =
    preserves-point-adjoint-structure-map-Spectrum n
```

### The structure maps of a spectrum

```agda
module _
  {l : Level} (A : Spectrum l) (n : ℕ)
  where

  pointed-structure-map-Spectrum :
    suspension-Pointed-Type (pointed-type-Spectrum A n) →∗
    pointed-type-Spectrum A (succ-ℕ n)
  pointed-structure-map-Spectrum =
    pointed-structure-map-Prespectrum (prespectrum-Spectrum A) n

  structure-map-Spectrum :
    suspension (type-Spectrum A n) → type-Spectrum A (succ-ℕ n)
  structure-map-Spectrum = map-pointed-map pointed-structure-map-Spectrum

  preserves-point-structure-map-Spectrum :
    structure-map-Spectrum north-suspension ＝ point-Spectrum A (succ-ℕ n)
  preserves-point-structure-map-Spectrum =
    preserves-point-pointed-map pointed-structure-map-Spectrum
```

## References

{{#bibliography}} {{#reference May99}}
