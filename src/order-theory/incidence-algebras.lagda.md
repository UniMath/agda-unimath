# Incidence algebras

```agda
open import foundation.function-extensionality-axiom

module
  order-theory.incidence-algebras
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings funext

open import foundation.dependent-pair-types
open import foundation.inhabited-types funext
open import foundation.universe-levels

open import foundation-core.cartesian-product-types

open import order-theory.interval-subposets funext
open import order-theory.locally-finite-posets funext
open import order-theory.posets funext
```

</details>

## Idea

For a [locally finite poset](order-theory.locally-finite-posets.md) `P` and
[commutative ring](commutative-algebra.commutative-rings.md) `R`, there is a
canonical `R`-associative algebra whose underlying `R`-module are the set-maps
from the nonempty [intervals](order-theory.interval-subposets.md) of `P` to `R`
(which we constructify as the inhabited intervals), and whose multiplication is
given by a "convolution" of maps. This is the **incidence algebra** of `P` over
`R`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) (loc-fin : is-locally-finite-Poset P)
  (x y : type-Poset P) (R : Commutative-Ring l3)
  where

  interval-map : UU (l1 ⊔ l2 ⊔ l3)
  interval-map = inhabited-interval P → type-Commutative-Ring R
```

WIP: complete this definition after _R-modules_ have been defined. Defining
convolution of maps would be aided as well with a lemma on 'unordered' addition
in abelian groups over finite sets.
