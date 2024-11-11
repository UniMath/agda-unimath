# Incidence algebras

```agda
module order-theory.incidence-algebras where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.function-commutative-rings

open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.universe-levels

open import order-theory.interval-subposets
open import order-theory.locally-finite-posets
open import order-theory.posets
```

</details>

## Idea

For a [locally finite poset](order-theory.locally-finite-posets) 'P' and
[commutative ring](commutative-algebra.commutative-rings) 'R', there is a
canonical 'R'-associative algebra whose undderlying 'R'-module are the set-maps
from 'P' to 'R', and whose multiplication is given by a "convolution" of maps.
This is the **incidence algebra** of 'P' over 'R'.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) (loc-fin : is-locally-finite-Poset P)
  (x y : type-Poset P) (R : Commutative-Ring l3)
  where

  interval-maps : UU _
  interval-maps = {! !} → type-Commutative-Ring R
```
