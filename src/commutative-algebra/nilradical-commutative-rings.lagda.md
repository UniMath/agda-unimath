# Nilradical of a commutative ring

```agda
module commutative-algebra.nilradical-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.nilpotent-elements-rings
```

</details>

## Idea

The **nilradical** of a commutative ring is the ideal consisting of all
nilpotent elements.

## Definitions

```agda
subset-nilradical-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) → subset-Commutative-Ring l A
subset-nilradical-Commutative-Ring A =
  is-nilpotent-element-ring-Prop (ring-Commutative-Ring A)
```

## Properties

### The nilradical contains zero

```agda
contains-zero-nilradical-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) →
  contains-zero-subset-Commutative-Ring A
    ( subset-nilradical-Commutative-Ring A)
contains-zero-nilradical-Commutative-Ring A = intro-∃ 1 refl
```

### The nilradical is closed under addition

```agda
is-closed-under-addition-nilradical-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) →
  is-closed-under-addition-subset-Commutative-Ring A
    ( subset-nilradical-Commutative-Ring A)
is-closed-under-addition-nilradical-Commutative-Ring A x y =
  is-nilpotent-add-Ring
    ( ring-Commutative-Ring A)
    ( x)
    ( y)
    ( commutative-mul-Commutative-Ring A x y)
```

### The nilradical is closed under negatives

```agda
is-closed-under-negatives-nilradical-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) →
  is-closed-under-negatives-subset-Commutative-Ring A
    ( subset-nilradical-Commutative-Ring A)
is-closed-under-negatives-nilradical-Commutative-Ring A x =
  is-nilpotent-element-neg-Ring (ring-Commutative-Ring A) x
```

### The nilradical is closed under multiplication with ring elements

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  is-closed-under-right-multiplication-nilradical-Commutative-Ring :
    is-closed-under-right-multiplication-subset-Commutative-Ring A
      ( subset-nilradical-Commutative-Ring A)
  is-closed-under-right-multiplication-nilradical-Commutative-Ring x y =
    is-nilpotent-element-mul-Ring
      ( ring-Commutative-Ring A)
      ( x)
      ( y)
      ( commutative-mul-Commutative-Ring A x y)

  is-closed-under-left-multiplication-nilradical-Commutative-Ring :
    is-closed-under-left-multiplication-subset-Commutative-Ring A
      ( subset-nilradical-Commutative-Ring A)
  is-closed-under-left-multiplication-nilradical-Commutative-Ring x y =
    is-nilpotent-element-mul-Ring'
      ( ring-Commutative-Ring A)
      ( y)
      ( x)
      ( commutative-mul-Commutative-Ring A y x)
```

### The nilradical ideal

```agda
nilradical-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) → ideal-Commutative-Ring l A
nilradical-Commutative-Ring A =
  ideal-right-ideal-Commutative-Ring A
    ( subset-nilradical-Commutative-Ring A)
    ( contains-zero-nilradical-Commutative-Ring A)
    ( is-closed-under-addition-nilradical-Commutative-Ring A)
    ( is-closed-under-negatives-nilradical-Commutative-Ring A)
    ( is-closed-under-right-multiplication-nilradical-Commutative-Ring A)
```
