# Connective spectra

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module synthetic-homotopy-theory.connective-spectra
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.connected-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.equivalences funext
open import foundation.function-types funext
open import foundation.identity-types funext
open import foundation.propositions funext univalence
open import foundation.truncation-levels
open import foundation.universe-levels

open import structured-types.pointed-equivalences funext univalence truncations
open import structured-types.pointed-maps funext univalence truncations
open import structured-types.pointed-types

open import synthetic-homotopy-theory.connective-prespectra funext univalence truncations
open import synthetic-homotopy-theory.loop-spaces funext univalence truncations
open import synthetic-homotopy-theory.prespectra funext univalence truncations
open import synthetic-homotopy-theory.spectra funext univalence truncations
open import synthetic-homotopy-theory.suspensions-of-pointed-types funext univalence truncations
open import synthetic-homotopy-theory.suspensions-of-types funext univalence truncations
```

</details>

## Idea

A [spectrum](synthetic-homotopy-theory.spectra.md) is
{{#concept "connective" Disambiguation="spectrum" Agda=is-connective-Spectrum}}
if the underlying [prespectrum](synthetic-homotopy-theory.prespectra.md) is
[connective](synthetic-homotopy-theory.connective-prespectra.md). I.e., if the
$n$th type in the [sequence](foundation.sequences.md) is
$n$-[connected](foundation.connected-types.md) for all $n$.

### The predicate on spectra of being connective

```agda
module _
  {l : Level} (A : Spectrum l)
  where

  is-connective-Spectrum : UU l
  is-connective-Spectrum = is-connective-Prespectrum (prespectrum-Spectrum A)

  is-prop-is-connective-Spectrum : is-prop is-connective-Spectrum
  is-prop-is-connective-Spectrum =
    is-prop-is-connective-Prespectrum (prespectrum-Spectrum A)

  is-connective-prop-Spectrum : Prop l
  is-connective-prop-Spectrum =
    is-connective-Spectrum , is-prop-is-connective-Spectrum
```

### The type of connective spectra

```agda
Connective-Spectrum : (l : Level) → UU (lsuc l)
Connective-Spectrum l = Σ (Spectrum l) (is-connective-Spectrum)

module _
  {l : Level} (A : Connective-Spectrum l)
  where

  spectrum-Connective-Spectrum : Spectrum l
  spectrum-Connective-Spectrum = pr1 A

  pointed-type-Connective-Spectrum : ℕ → Pointed-Type l
  pointed-type-Connective-Spectrum =
    pointed-type-Spectrum spectrum-Connective-Spectrum

  type-Connective-Spectrum : ℕ → UU l
  type-Connective-Spectrum =
    type-Spectrum spectrum-Connective-Spectrum

  point-Connective-Spectrum : (n : ℕ) → type-Connective-Spectrum n
  point-Connective-Spectrum =
    point-Spectrum spectrum-Connective-Spectrum

  pointed-adjoint-structure-map-Connective-Spectrum :
    (n : ℕ) →
    pointed-type-Connective-Spectrum n →∗
    Ω (pointed-type-Connective-Spectrum (succ-ℕ n))
  pointed-adjoint-structure-map-Connective-Spectrum =
    pointed-adjoint-structure-map-Spectrum spectrum-Connective-Spectrum

  adjoint-structure-map-Connective-Spectrum :
    (n : ℕ) →
    type-Connective-Spectrum n →
    type-Ω (pointed-type-Connective-Spectrum (succ-ℕ n))
  adjoint-structure-map-Connective-Spectrum =
    adjoint-structure-map-Spectrum spectrum-Connective-Spectrum

  preserves-point-adjoint-structure-map-Connective-Spectrum :
    (n : ℕ) →
    adjoint-structure-map-Spectrum (pr1 A) n (point-Spectrum (pr1 A) n) ＝
    refl-Ω (pointed-type-Spectrum (pr1 A) (succ-ℕ n))
  preserves-point-adjoint-structure-map-Connective-Spectrum =
    preserves-point-adjoint-structure-map-Spectrum
      spectrum-Connective-Spectrum

  is-equiv-pointed-adjoint-structure-map-Connective-Spectrum :
    (n : ℕ) →
    is-pointed-equiv (pointed-adjoint-structure-map-Connective-Spectrum n)
  is-equiv-pointed-adjoint-structure-map-Connective-Spectrum =
    is-equiv-pointed-adjoint-structure-map-Spectrum spectrum-Connective-Spectrum

  structure-equiv-Connective-Spectrum :
    (n : ℕ) →
    type-Connective-Spectrum n ≃
    type-Ω (pointed-type-Connective-Spectrum (succ-ℕ n))
  structure-equiv-Connective-Spectrum n =
    adjoint-structure-map-Connective-Spectrum n ,
    is-equiv-pointed-adjoint-structure-map-Connective-Spectrum n

  pointed-structure-equiv-Connective-Spectrum :
    (n : ℕ) →
    pointed-type-Connective-Spectrum n ≃∗
    Ω (pointed-type-Connective-Spectrum (succ-ℕ n))
  pointed-structure-equiv-Connective-Spectrum n =
    structure-equiv-Connective-Spectrum n ,
    preserves-point-adjoint-structure-map-Connective-Spectrum n

  is-connective-Connective-Spectrum :
    is-connective-Spectrum spectrum-Connective-Spectrum
  is-connective-Connective-Spectrum = pr2 A
```

### The structure maps of a connective spectrum

```agda
module _
  {l : Level} (A : Connective-Spectrum l) (n : ℕ)
  where

  pointed-structure-map-Connective-Spectrum :
    suspension-Pointed-Type (pointed-type-Connective-Spectrum A n) →∗
    pointed-type-Connective-Spectrum A (succ-ℕ n)
  pointed-structure-map-Connective-Spectrum =
    pointed-structure-map-Spectrum (spectrum-Connective-Spectrum A) n

  structure-map-Connective-Spectrum :
    suspension (type-Connective-Spectrum A n) →
    type-Connective-Spectrum A (succ-ℕ n)
  structure-map-Connective-Spectrum =
    map-pointed-map pointed-structure-map-Connective-Spectrum

  preserves-point-structure-map-Connective-Spectrum :
    structure-map-Connective-Spectrum north-suspension ＝
    point-Connective-Spectrum A (succ-ℕ n)
  preserves-point-structure-map-Connective-Spectrum =
    preserves-point-pointed-map pointed-structure-map-Connective-Spectrum
```

## External links

- [connective spectrum](https://ncatlab.org/nlab/show/connective+spectrum) at
  $n$Lab
