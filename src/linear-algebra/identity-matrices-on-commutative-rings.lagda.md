# Identity matrices on commutative rings

```agda
module linear-algebra.identity-matrices-on-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.identity-matrices-on-rings
open import linear-algebra.square-matrices-on-commutative-rings
```

</details>

## Idea

The `n × n`
{{#concept "identity matrix" Disambiguation="on a commutative ring" WDID=Q193794 WD="identity matrix" Agda=id-matrix-Commutative-Ring}}
on a [commutative ring](commutative-algebra.commutative-rings.md) is the
[diagonal matrix](linear-algebra.diagonal-matrices-on-rings.md) with all 1s on
the diagonal.

## Definition

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (n : ℕ)
  where

  id-matrix-Commutative-Ring : square-matrix-Commutative-Ring R n
  id-matrix-Commutative-Ring = id-matrix-Ring (ring-Commutative-Ring R) n
```
