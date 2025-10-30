# Characteristics of rings

```agda
module ring-theory.characteristics-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.ring-of-integers

open import foundation.universe-levels

open import ring-theory.ideals-rings
open import ring-theory.kernels-of-ring-homomorphisms
open import ring-theory.rings
```

</details>

## Idea

The
{{#concept "characteristic" Disambiguation="of a ring" WD="characteristic" WDID=Q836088 Agda=characteristic-Ring}}
of a [ring](ring-theory.rings.md) `R` is defined to be the kernel of the
[initial ring homomorphism](elementary-number-theory.ring-of-integers.md) from
the [ring `ℤ` of integers](elementary-number-theory.ring-of-integers.md) to `R`.

## Definitions

### Characteristics of rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  characteristic-Ring : ideal-Ring l ℤ-Ring
  characteristic-Ring = kernel-hom-Ring ℤ-Ring R (initial-hom-Ring R)
```
