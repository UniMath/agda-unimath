# Identity matrices on rings

```agda
module linear-algebra.identity-matrices-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.diagonal-matrices-on-rings
open import linear-algebra.square-matrices-on-rings

open import ring-theory.rings
```

</details>

## Idea

The `n × n`
{{#concept "identity matrix" Disambiguation="on a ring" WDID=Q193794 WD="identity matrix" Agda=id-matrix-Ring}}
on a [ring](ring-theory.rings.md) is the
[diagonal matrix](linear-algebra.diagonal-matrices-on-rings.md) with all 1s on
the diagonal.

## Definition

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  where

  id-matrix-Ring : square-matrix-Ring R n
  id-matrix-Ring =
    matrix-from-diagonal-fin-sequence-type-Ring R n (λ _ → one-Ring R)
```
