# Incidence algebras

```agda
module order-theory.incidence-algebras where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types

open import order-theory.interval-subposets
open import order-theory.locally-finite-posets
open import order-theory.posets
```

</details>

## Idea

For a [locally finite poset](order-theory.locally-finite-posets) 'P' and
[commutative ring](commutative-algebra.commutative-rings) 'R', there is a
canonical 'R'-associative algebra whose undderlying 'R'-module are the set-maps
from the nonempty intervals of 'P' to 'R' (which we constructify as the
inhabited intervals), and whose multiplication is given by a "convolution" of
maps. This is the **incidence algebra** of 'P' over 'R'.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) (loc-fin : is-locally-finite-Poset P)
  (x y : type-Poset P) (R : Commutative-Ring l3)
  where

  is-inhabited-interval : UU (l1 ⊔ l2)
  is-inhabited-interval =
    is-inhabited (type-Poset (poset-interval-Subposet P x y))

  inhabited-intervals : UU (l1 ⊔ l2)
  inhabited-intervals =
    Σ (type-Poset P × type-Poset P) (λ (p , q) → is-inhabited-interval)

  interval-maps : UU (l1 ⊔ l2 ⊔ l3)
  interval-maps = inhabited-intervals → type-Commutative-Ring R
```

WIP: complete this definition after _R-modules_ have been defined. Defining
convolution of maps would be aided as well with a lemma on 'unordered' addition
in abelian groups over finite sets.
