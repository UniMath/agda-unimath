# Spheres

```agda
module synthetic-homotopy-theory.spheres where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.suspensions-of-types

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The spheres are defined as iterated suspensions of `Fin 2`.

## Definition

```agda
sphere : ℕ → UU lzero
sphere zero-ℕ = Fin 2
sphere (succ-ℕ n) = suspension (sphere n)

north-sphere : (n : ℕ) → sphere n
north-sphere zero-ℕ = zero-Fin 1
north-sphere (succ-ℕ n) = north-suspension

south-sphere : (n : ℕ) → sphere n
south-sphere zero-ℕ = one-Fin 1
south-sphere (succ-ℕ n) = south-suspension

meridian-sphere :
  (n : ℕ) → sphere n →
  north-sphere (succ-ℕ n) ＝ south-sphere (succ-ℕ n)
meridian-sphere n = meridian-suspension
```
