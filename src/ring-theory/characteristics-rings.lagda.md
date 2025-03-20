# Characteristics of rings

```agda
open import foundation.function-extensionality-axiom

module
  ring-theory.characteristics-rings
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.ring-of-integers funext

open import foundation.universe-levels

open import ring-theory.ideals-rings funext
open import ring-theory.kernels-of-ring-homomorphisms funext
open import ring-theory.rings funext
```

</details>

## Idea

The **characteristic** of a [ring](ring-theory.rings.md) `R` is defined to be
the kernel of the
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
