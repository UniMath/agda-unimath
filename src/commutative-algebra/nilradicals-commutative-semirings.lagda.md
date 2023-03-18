# The nilradical of a commutative semiring

```agda
module commutative-algebra.nilradicals-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.subsets-commutative-semirings

open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.nilpotent-elements-semirings
```

</details>

## Idea

The nilradical of a commutative semiring is the ideal consisting of all
nilpotent elements.

## Definitions

```agda
subset-nilradical-Commutative-Semiring :
  {l : Level} (R : Commutative-Semiring l) → subset-Commutative-Semiring l R
subset-nilradical-Commutative-Semiring R =
  is-nilpotent-element-semiring-Prop (semiring-Commutative-Semiring R)
```

## Properties

### The nilradical contains zero

```agda
contains-zero-nilradical-Commutative-Semiring :
  {l : Level} (R : Commutative-Semiring l) →
  contains-zero-subset-Commutative-Semiring R
    ( subset-nilradical-Commutative-Semiring R)
contains-zero-nilradical-Commutative-Semiring R = intro-∃ 1 refl
```

### The nilradical is closed under addition

```agda
is-closed-under-add-nilradical-Commutative-Semiring :
  {l : Level} (R : Commutative-Semiring l) →
  is-closed-under-addition-subset-Commutative-Semiring R
    ( subset-nilradical-Commutative-Semiring R)
is-closed-under-add-nilradical-Commutative-Semiring R x y =
  is-nilpotent-add-Semiring
    ( semiring-Commutative-Semiring R)
    ( x)
    ( y)
    ( commutative-mul-Commutative-Semiring R x y)
```

### The nilradical is closed under multiplication with ring elements

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  is-closed-under-mul-right-nilradical-Commutative-Semiring :
    is-closed-under-right-multiplication-subset-Commutative-Semiring R
      ( subset-nilradical-Commutative-Semiring R)
  is-closed-under-mul-right-nilradical-Commutative-Semiring x y =
    is-nilpotent-element-mul-Semiring
      ( semiring-Commutative-Semiring R)
      ( x)
      ( y)
      ( commutative-mul-Commutative-Semiring R x y)

  is-closed-under-mul-left-nilradical-Commutative-Semiring :
    is-closed-under-left-multiplication-subset-Commutative-Semiring R
      ( subset-nilradical-Commutative-Semiring R)
  is-closed-under-mul-left-nilradical-Commutative-Semiring x y =
    is-nilpotent-element-mul-Semiring'
      ( semiring-Commutative-Semiring R)
      ( y)
      ( x)
      ( commutative-mul-Commutative-Semiring R y x)
```
