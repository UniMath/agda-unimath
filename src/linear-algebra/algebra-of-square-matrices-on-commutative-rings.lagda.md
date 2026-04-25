# The algebra of square matrices on commutative rings

```agda
module linear-algebra.algebra-of-square-matrices-on-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.algebras-commutative-rings
open import commutative-algebra.associative-algebras-commutative-rings
open import commutative-algebra.commutative-rings
open import commutative-algebra.unital-associative-algebras-commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.monoids

open import linear-algebra.identity-matrices-on-commutative-rings
open import linear-algebra.multiplication-square-matrices-on-commutative-rings
open import linear-algebra.square-matrices-on-commutative-rings

open import ring-theory.rings
```

</details>

## Idea

[Square matrices](linear-algebra.square-matrices-on-commutative-rings.md) on
[commutative rings](commutative-algebra.commutative-rings.md) form a
[unital associative algebra](commutative-algebra.unital-associative-algebras-commutative-rings.md)
under
[matrix multiplication](linear-algebra.multiplication-square-matrices-on-commutative-rings.md).

## Definition

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (n : ℕ)
  where

  algebra-square-matrix-Commutative-Ring : algebra-Commutative-Ring l R
  algebra-square-matrix-Commutative-Ring =
    ( left-module-square-matrix-Commutative-Ring R n ,
      bilinear-map-mul-square-matrix-Commutative-Ring R n)

  associative-algebra-square-matrix-Commutative-Ring :
    associative-algebra-Commutative-Ring l R
  associative-algebra-square-matrix-Commutative-Ring =
    ( algebra-square-matrix-Commutative-Ring ,
      associative-mul-square-matrix-Commutative-Ring R n)

  unital-associative-algebra-square-matrix-Commutative-Ring :
    unital-associative-algebra-Commutative-Ring l R
  unital-associative-algebra-square-matrix-Commutative-Ring =
    ( associative-algebra-square-matrix-Commutative-Ring ,
      id-matrix-Commutative-Ring R n ,
      left-unit-law-mul-square-matrix-Commutative-Ring R n ,
      right-unit-law-mul-square-matrix-Commutative-Ring R n)

  monoid-mul-square-matrix-Commutative-Ring : Monoid l
  monoid-mul-square-matrix-Commutative-Ring =
    monoid-mul-unital-associative-algebra-Commutative-Ring
      ( R)
      ( unital-associative-algebra-square-matrix-Commutative-Ring)

  ring-square-matrix-Commutative-Ring : Ring l
  ring-square-matrix-Commutative-Ring =
    ring-unital-associative-algebra-Commutative-Ring
      ( R)
      ( unital-associative-algebra-square-matrix-Commutative-Ring)
```
