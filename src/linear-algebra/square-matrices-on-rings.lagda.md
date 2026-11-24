# Square matrices on rings

```agda
module linear-algebra.square-matrices-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups

open import linear-algebra.left-modules-rings
open import linear-algebra.matrices-on-rings

open import ring-theory.rings
```

</details>

## Idea

A
{{#concept "square matrix" Disambiguation="over a ring" WDID=Q2739329 WD="square matrix" Agda=square-matrix-Ring}}
on a [ring](ring-theory.rings.md) `R` is a
[matrix](linear-algebra.matrices-on-rings.md) over `R` that is `n × n` for some
`n`.

## Definition

```agda
square-matrix-Ring : {l : Level} → Ring l → ℕ → UU l
square-matrix-Ring R n = matrix-Ring R n n
```

## Properties

### Square matrices in a ring form a set

```agda
set-square-matrix-Ring : {l : Level} → Ring l → ℕ → Set l
set-square-matrix-Ring R n = set-matrix-Ring R n n
```

### Square matrices on a ring form a left module

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  where

  left-module-square-matrix-Ring : left-module-Ring l R
  left-module-square-matrix-Ring = left-module-matrix-Ring R n n

  ab-square-matrix-Ring : Ab l
  ab-square-matrix-Ring = ab-matrix-Ring R n n
```
