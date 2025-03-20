# The sphere prespectrum

```agda
open import foundation.function-extensionality-axiom

module
  synthetic-homotopy-theory.sphere-prespectrum
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.prespectra funext
open import synthetic-homotopy-theory.suspension-prespectra funext

open import univalent-combinatorics.standard-finite-types funext
```

</details>

## Idea

The [spheres](synthetic-homotopy-theory.spheres.md) `Sⁿ` define a
[prespectrum](synthetic-homotopy-theory.prespectra.md)

```text
  Sⁿ →∗ ΩSⁿ⁺¹
```

which we call the **sphere prespectrum**.

**Note:** Even though the sphere prespectrum is defined degreewise by the
adjoint to the identity map, it is not in general a
[spectrum](synthetic-homotopy-theory.spectra.md), as the transposing map of the
[loop-suspension adjunction](synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types.md)
does not generally send [equivalences](foundation-core.equivalences.md) to
equivalences.

## Definition

### The sphere prespectrum

```agda
sphere-Prespectrum : Prespectrum lzero
sphere-Prespectrum = suspension-Prespectrum (Fin 2 , zero-Fin 1)
```
