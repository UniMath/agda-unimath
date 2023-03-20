# Nilradical of a commutative ring

```agda
module commutative-algebra.nilradical-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.binomial-theorem-commutative-rings
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.powers-of-elements-commutative-rings
open import commutative-algebra.subsets-commutative-rings
open import commutative-algebra.sums-commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.binomial-coefficients
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.nilpotent-elements-rings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The nilradical of a commutative ring is the ideal consisting of all nilpotent
elements.

## Definitions

```agda
subset-nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) → subset-Commutative-Ring l R
subset-nilradical-Commutative-Ring R =
  is-nilpotent-element-ring-Prop (ring-Commutative-Ring R)
```

## Properties

### The nilradical contains zero

```agda
contains-zero-nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  contains-zero-subset-Commutative-Ring R
    ( subset-nilradical-Commutative-Ring R)
contains-zero-nilradical-Commutative-Ring R = intro-∃ 1 refl
```

### The nilradical is closed under addition

```agda
is-closed-under-addition-nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  is-closed-under-addition-subset-Commutative-Ring R
    ( subset-nilradical-Commutative-Ring R)
is-closed-under-addition-nilradical-Commutative-Ring R x y =
  is-nilpotent-add-Ring
    ( ring-Commutative-Ring R)
    ( x)
    ( y)
    ( commutative-mul-Commutative-Ring R x y)
```

### The nilradical is closed under negatives

```agda
is-closed-under-negatives-nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  is-closed-under-negatives-subset-Commutative-Ring R
    ( subset-nilradical-Commutative-Ring R)
is-closed-under-negatives-nilradical-Commutative-Ring R x =
  is-nilpotent-element-neg-Ring (ring-Commutative-Ring R) x
```

### The nilradical is closed under multiplication with ring elements

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  is-closed-under-right-multiplication-nilradical-Commutative-Ring :
    is-closed-under-right-multiplication-subset-Commutative-Ring R
      ( subset-nilradical-Commutative-Ring R)
  is-closed-under-right-multiplication-nilradical-Commutative-Ring x y =
    is-nilpotent-element-mul-Ring
      ( ring-Commutative-Ring R)
      ( x)
      ( y)
      ( commutative-mul-Commutative-Ring R x y)

  is-closed-under-left-multiplication-nilradical-Commutative-Ring :
    is-closed-under-left-multiplication-subset-Commutative-Ring R
      ( subset-nilradical-Commutative-Ring R)
  is-closed-under-left-multiplication-nilradical-Commutative-Ring x y =
    is-nilpotent-element-mul-Ring'
      ( ring-Commutative-Ring R)
      ( y)
      ( x)
      ( commutative-mul-Commutative-Ring R y x)
```

### The nilradical ideal

```agda
nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) → ideal-Commutative-Ring l R
nilradical-Commutative-Ring R =
  ideal-right-ideal-Commutative-Ring R
    ( subset-nilradical-Commutative-Ring R)
    ( contains-zero-nilradical-Commutative-Ring R)
    ( is-closed-under-addition-nilradical-Commutative-Ring R)
    ( is-closed-under-negatives-nilradical-Commutative-Ring R)
    ( is-closed-under-right-multiplication-nilradical-Commutative-Ring R)
```
