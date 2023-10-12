# Spheres

```agda
module synthetic-homotopy-theory.spheres where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.iterated-suspensions-of-pointed-types
open import synthetic-homotopy-theory.suspensions-of-types

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The **spheres** are defined as
[iterated suspensions](synthetic-homotopy-theory.iterated-suspensions-of-pointed-types.md)
of the
[standard two-element type `Fin 2`](univalent-combinatorics.standard-finite-types.md).

## Definition

```agda
sphere-Pointed-Type : ℕ → Pointed-Type lzero
sphere-Pointed-Type n = iterated-suspension-Pointed-Type n (Fin 2 , zero-Fin 1)

sphere : ℕ → UU lzero
sphere = type-Pointed-Type ∘ sphere-Pointed-Type

north-sphere : (n : ℕ) → sphere n
north-sphere zero-ℕ = zero-Fin 1
north-sphere (succ-ℕ n) = north-suspension

south-sphere : (n : ℕ) → sphere n
south-sphere zero-ℕ = one-Fin 1
south-sphere (succ-ℕ n) = south-suspension

meridian-sphere :
  (n : ℕ) → sphere n → north-sphere (succ-ℕ n) ＝ south-sphere (succ-ℕ n)
meridian-sphere n = meridian-suspension
```
