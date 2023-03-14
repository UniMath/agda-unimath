# Spheres

```agda
module synthetic-homotopy-theory.spheres where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

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

N-sphere : (n : ℕ) → sphere n
N-sphere zero-ℕ = zero-Fin 1
N-sphere (succ-ℕ n) = N-susp

S-sphere : (n : ℕ) → sphere n
S-sphere zero-ℕ = one-Fin 1
S-sphere (succ-ℕ n) = S-susp
```
