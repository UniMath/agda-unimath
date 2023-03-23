# Nilradical of a commutative ring

```agda
module commutative-algebra.nilradical-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.subsets-commutative-rings
open import commutative-algebra.subsets-commutative-rings
open import commutative-algebra.prime-ideals-commutative-rings

open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.propositions


open import ring-theory.nilpotent-elements-rings
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

### The nilradical is contained in every prime ideal

```agda

is-in-nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) → type-Commutative-Ring R → UU l
is-in-nilradical-Commutative-Ring R =
  is-in-ideal-Commutative-Ring R (nilradical-Commutative-Ring R)

is-in-nilradical-Commutative-Ring-Prop :
  {l : Level} (R : Commutative-Ring l) → type-Commutative-Ring R → Prop l
is-in-nilradical-Commutative-Ring-Prop R =
  is-nilpotent-element-ring-Prop (ring-Commutative-Ring R)
  {-∃-Prop ℕ (λ n → power-Commutative-Ring R n x ＝ zero-Commutative-Ring R)-}


is-contained-in-prime-ideal-nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l)
  (P : prime-ideal-Commutative-Ring l R) (x : type-Commutative-Ring R) →
  is-in-nilradical-Commutative-Ring R x →
  is-in-prime-ideal-Commutative-Ring R P x
is-contained-in-prime-ideal-nilradical-Commutative-Ring R P x p =
  apply-universal-property-trunc-Prop p
  {!  !}
  (λ n → {!  !})

```
