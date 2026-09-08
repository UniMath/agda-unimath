# The rings of square matrices on rings

```agda
module linear-algebra.rings-of-square-matrices-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.monoids

open import linear-algebra.identity-matrices-on-rings
open import linear-algebra.multiplication-matrices-on-rings
open import linear-algebra.multiplication-square-matrices-on-rings
open import linear-algebra.square-matrices-on-rings

open import ring-theory.rings
```

</details>

## Idea

For any `n : ℕ`, `n × n`
[square matrices](linear-algebra.square-matrices-on-rings.md) on a
[ring](ring-theory.rings.md) `R` themselves form a ring under
[multiplication](linear-algebra.multiplication-square-matrices-on-rings.md).

## Definition

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  where

  ring-square-matrix-Ring : Ring l
  ring-square-matrix-Ring =
    ( ab-square-matrix-Ring R n ,
      ( mul-square-matrix-Ring R n ,
        associative-mul-square-matrix-Ring R n) ,
      ( id-matrix-Ring R n ,
        left-unit-law-mul-square-matrix-Ring R n ,
        right-unit-law-mul-square-matrix-Ring R n) ,
      left-distributive-mul-add-matrix-Ring R n n n ,
      right-distributive-mul-add-matrix-Ring R n n n)

  monoid-mul-square-matrix-Ring : Monoid l
  monoid-mul-square-matrix-Ring =
    multiplicative-monoid-Ring ring-square-matrix-Ring
```

## See also

- [The algebra of multiplication of square matrices on commutative rings](linear-algebra.algebra-of-square-matrices-on-commutative-rings.md)
