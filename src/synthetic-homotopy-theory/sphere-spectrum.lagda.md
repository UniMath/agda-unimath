# The sphere spectrum

```agda
module synthetic-homotopy-theory.sphere-spectrum where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.prespectra
open import synthetic-homotopy-theory.suspension-prespectra

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The [spheres](synthetic-homotopy-theory.spheres.md) `Sⁿ` define a
[spectrum](synthetic-homotopy-theory.spectra.md)

```text
  Sⁿ ≃∗ ΩSⁿ⁺¹
```

which we call the **sphere spectrum**.

## Definition

### The sphere prespectrum

```agda
sphere-Prespectrum : Prespectrum lzero
sphere-Prespectrum = suspension-Prespectrum (Fin 2 , zero-Fin 1)
```

### The sphere spectrum

This remains to be defined. To define this, it would be practical to first have
the lemma that the transposing map of the loop-suspension adjunction preserves
and reflects equivalences. Then we can simply use the transpose of the identity
function as our structure map.
