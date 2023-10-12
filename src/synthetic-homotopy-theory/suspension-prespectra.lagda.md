# Suspension prespectra

```agda
module synthetic-homotopy-theory.suspension-prespectra where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.iterated-suspensions-of-pointed-types
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.prespectra
open import synthetic-homotopy-theory.spectra
open import synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types
```

</details>

## Idea

Given a [pointed type](structured-types.pointed-types.md) `A`, the
[sequence](foundation.sequences.md) of iterated
[suspensions](synthetic-homotopy-theory.suspensions-of-pointed-types.md) of `A`

```text
  A   Σ¹A   Σ² A   Σ³ A   ...
```

defines a [prespectrum](synthetic-homotopy-theory.prespectra.md) that we call
the **suspension spectrum** of `A`.

## Definition

```agda
suspension-Prespectrum : {l : Level} → Pointed-Type l → Prespectrum l
pr1 (suspension-Prespectrum A) n = iterated-suspension-Pointed-Type n A
pr2 (suspension-Prespectrum A) n =
  pointed-map-unit-susp-loop-adj (iterated-suspension-Pointed-Type n A)
```
