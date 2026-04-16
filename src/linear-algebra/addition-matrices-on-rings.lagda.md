# Addition of matrices on rings

```agda
module linear-algebra.addition-matrices-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.function-abelian-groups

open import linear-algebra.matrices-on-rings
open import linear-algebra.square-matrices-on-rings

open import ring-theory.rings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Addition of [matrices](linear-algebra.matrices-on-rings.md) on a
[ring](ring-theory.rings.md) is done coordinatewise, with
`(A + B)ᵢⱼ = Aᵢⱼ + Bᵢⱼ`. Matrices on a ring form an
[abelian group](group-theory.abelian-groups.md) under addition.

## Definition

```agda
module _
  {l : Level}
  (R : Ring l)
  (m n : ℕ)
  where

  ab-add-matrix-Ring : Ab l
  ab-add-matrix-Ring =
    function-Ab (function-Ab (ab-Ring R) (Fin n)) (Fin m)

  add-matrix-Ring : matrix-Ring R m n → matrix-Ring R m n → matrix-Ring R m n
  add-matrix-Ring = add-Ab ab-add-matrix-Ring

module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  where

  ab-add-square-matrix-Ring : Ab l
  ab-add-square-matrix-Ring = ab-add-matrix-Ring R n n

  add-square-matrix-Ring :
    square-matrix-Ring R n → square-matrix-Ring R n → square-matrix-Ring R n
  add-square-matrix-Ring = add-Ab ab-add-square-matrix-Ring
```
