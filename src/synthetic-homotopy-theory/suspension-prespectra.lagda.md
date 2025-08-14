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
open import synthetic-homotopy-theory.suspensions-of-pointed-types
open import synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types
```

</details>

## Idea

Given a [pointed type](structured-types.pointed-types.md) `A`, the
[sequence](lists.sequences.md) of
[iterated suspensions](synthetic-homotopy-theory.iterated-suspensions-of-pointed-types.md)
of `A`

```text
  A   Σ¹A   Σ²A   Σ³A   ...
```

defines a [prespectrum](synthetic-homotopy-theory.prespectra.md) `Σ^∞A` that we
call the **suspension prespectrum** of `A`. Its structure map is defined
degreewise by the identity

```text
  Σⁿ⁺¹A = Σⁿ⁺¹A   ↝   ΣⁿA →∗ ΩΣⁿ⁺¹A
```

**Note:** Even though the suspension prespectrum is defined degreewise by the
adjoint to the identity map, it is not in general a
[spectrum](synthetic-homotopy-theory.spectra.md), as the transposing map of the
[loop-suspension adjunction](synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types.md)
does not generally send [equivalences](foundation-core.equivalences.md) to
equivalences.

## Definition

```agda
pointed-structure-map-suspension-Prespectrum :
  {l : Level} (A : Pointed-Type l) (n : ℕ) →
  suspension-Pointed-Type (iterated-suspension-Pointed-Type n A) →∗
  iterated-suspension-Pointed-Type (succ-ℕ n) A
pointed-structure-map-suspension-Prespectrum A n = id-pointed-map

pointed-adjoint-structure-map-suspension-Prespectrum :
  {l : Level} (A : Pointed-Type l) (n : ℕ) →
  iterated-suspension-Pointed-Type n A →∗
  Ω (iterated-suspension-Pointed-Type (succ-ℕ n) A)
pointed-adjoint-structure-map-suspension-Prespectrum A n =
  transpose-suspension-loop-adjunction
    ( iterated-suspension-Pointed-Type n A)
    ( iterated-suspension-Pointed-Type (succ-ℕ n) A)
    ( pointed-structure-map-suspension-Prespectrum A n)

suspension-Prespectrum : {l : Level} → Pointed-Type l → Prespectrum l
pr1 (suspension-Prespectrum A) n = iterated-suspension-Pointed-Type n A
pr2 (suspension-Prespectrum A) =
  pointed-adjoint-structure-map-suspension-Prespectrum A
```
