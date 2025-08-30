# Connective prespectra

```agda
module synthetic-homotopy-theory.connective-prespectra where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.truncation-levels
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

A [prespectrum](synthetic-homotopy-theory.prespectra.md) is
{{#concept "connective" Disambiguation="prespectrum" Agda=is-connective-Prespectrum}}
if the $n$th type in the [sequence](lists.sequences.md) is
$n$-[connected](foundation.connected-types.md).

### The predicate on prespectra of being connective

```agda
module _
  {l : Level} (A : Prespectrum l)
  where

  is-connective-Prespectrum : UU l
  is-connective-Prespectrum =
    (n : ℕ) → is-connected (truncation-level-ℕ n) (type-Prespectrum A n)

  is-prop-is-connective-Prespectrum : is-prop is-connective-Prespectrum
  is-prop-is-connective-Prespectrum =
    is-prop-Π
      ( λ n →
        is-prop-is-connected (truncation-level-ℕ n) (type-Prespectrum A n))

  is-connective-prop-Prespectrum : Prop l
  is-connective-prop-Prespectrum =
    is-connective-Prespectrum , is-prop-is-connective-Prespectrum
```

### The type of connective prespectra

```agda
Connective-Prespectrum : (l : Level) → UU (lsuc l)
Connective-Prespectrum l = Σ (Prespectrum l) (is-connective-Prespectrum)

module _
  {l : Level} (A : Connective-Prespectrum l)
  where

  prespectrum-Connective-Prespectrum : Prespectrum l
  prespectrum-Connective-Prespectrum = pr1 A

  pointed-type-Connective-Prespectrum : ℕ → Pointed-Type l
  pointed-type-Connective-Prespectrum =
    pointed-type-Prespectrum prespectrum-Connective-Prespectrum

  type-Connective-Prespectrum : ℕ → UU l
  type-Connective-Prespectrum =
    type-Prespectrum prespectrum-Connective-Prespectrum

  point-Connective-Prespectrum : (n : ℕ) → type-Connective-Prespectrum n
  point-Connective-Prespectrum =
    point-Prespectrum prespectrum-Connective-Prespectrum

  pointed-adjoint-structure-map-Connective-Prespectrum :
    (n : ℕ) →
    pointed-type-Connective-Prespectrum n →∗
    Ω (pointed-type-Connective-Prespectrum (succ-ℕ n))
  pointed-adjoint-structure-map-Connective-Prespectrum =
    pointed-adjoint-structure-map-Prespectrum prespectrum-Connective-Prespectrum

  adjoint-structure-map-Connective-Prespectrum :
    (n : ℕ) →
    type-Connective-Prespectrum n →
    type-Ω (pointed-type-Connective-Prespectrum (succ-ℕ n))
  adjoint-structure-map-Connective-Prespectrum =
    adjoint-structure-map-Prespectrum prespectrum-Connective-Prespectrum

  preserves-point-adjoint-structure-map-Connective-Prespectrum :
    (n : ℕ) →
    adjoint-structure-map-Prespectrum (pr1 A) n (point-Prespectrum (pr1 A) n) ＝
    refl-Ω (pointed-type-Prespectrum (pr1 A) (succ-ℕ n))
  preserves-point-adjoint-structure-map-Connective-Prespectrum =
    preserves-point-adjoint-structure-map-Prespectrum
      prespectrum-Connective-Prespectrum

  is-connective-Connective-Prespectrum :
    is-connective-Prespectrum prespectrum-Connective-Prespectrum
  is-connective-Connective-Prespectrum = pr2 A
```

### The structure maps of a connective prespectrum

```agda
module _
  {l : Level} (A : Connective-Prespectrum l) (n : ℕ)
  where

  pointed-structure-map-Connective-Prespectrum :
    suspension-Pointed-Type (pointed-type-Connective-Prespectrum A n) →∗
    pointed-type-Connective-Prespectrum A (succ-ℕ n)
  pointed-structure-map-Connective-Prespectrum =
    pointed-structure-map-Prespectrum (prespectrum-Connective-Prespectrum A) n

  structure-map-Connective-Prespectrum :
    suspension (type-Connective-Prespectrum A n) →
    type-Connective-Prespectrum A (succ-ℕ n)
  structure-map-Connective-Prespectrum =
    map-pointed-map pointed-structure-map-Connective-Prespectrum

  preserves-point-structure-map-Connective-Prespectrum :
    structure-map-Connective-Prespectrum north-suspension ＝
    point-Connective-Prespectrum A (succ-ℕ n)
  preserves-point-structure-map-Connective-Prespectrum =
    preserves-point-pointed-map pointed-structure-map-Connective-Prespectrum
```

## External links

- [connective spectrum](https://ncatlab.org/nlab/show/connective+spectrum) at
  $n$Lab
