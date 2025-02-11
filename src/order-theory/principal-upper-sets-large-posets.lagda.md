# Principal upper sets of large posets

```agda
module order-theory.principal-upper-sets-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-subposets
open import order-theory.large-subpreorders
open import order-theory.similarity-of-elements-large-posets
```

</details>

## Idea

The **principal upper set** `↑{x}` of an element `x` of a
[large poset](order-theory.large-posets.md) `P` is the
[large subposet](order-theory.large-subposets.md) consisting of all elements
`x ≤ y` in `P`.

Two elements `x` and `y` in a large poset `P` are
[similar](order-theory.similarity-of-elements-large-posets.md) if and only if
they have the same principal upper sets, and if `x` and `y` are of the same
[universe level](foundation.universe-levels.md), then `x` and `y` are equal if
and only if they have the same principal upper sets. To see this, note that if
`↑{x} = ↑{y}`, then we have the implications `(x ≤ x) → (x ≤ y)` and
`(y ≤ y) → (y ≤ x)`.

## Definitions

### The predicate of being a principal upper set of an element

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  {l1 : Level} (x : type-Large-Poset P l1)
  {γ : Level → Level} (S : Large-Subposet γ P)
  where

  is-principal-upper-set-Large-Subposet : UUω
  is-principal-upper-set-Large-Subposet =
    {l : Level} (y : type-Large-Poset P l) →
    leq-Large-Poset P y x ↔ is-in-Large-Subposet P S y
```

### The principal upper set of an element

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  {l1 : Level} (x : type-Large-Poset P l1)
  where

  large-subpreorder-principal-upper-set-element-Large-Poset :
    Large-Subpreorder (λ l → β l1 l) (large-preorder-Large-Poset P)
  large-subpreorder-principal-upper-set-element-Large-Poset y =
    leq-prop-Large-Poset P x y

  is-closed-under-sim-principal-upper-set-element-Large-Poset :
    is-closed-under-sim-Large-Subpreorder P
      ( large-subpreorder-principal-upper-set-element-Large-Poset)
  is-closed-under-sim-principal-upper-set-element-Large-Poset y z p q l =
    transitive-leq-Large-Poset P x y z p l

  principal-upper-set-element-Large-Poset : Large-Subposet (λ l → β l1 l) P
  large-subpreorder-Large-Subposet principal-upper-set-element-Large-Poset =
    large-subpreorder-principal-upper-set-element-Large-Poset
  is-closed-under-sim-Large-Subposet principal-upper-set-element-Large-Poset =
    is-closed-under-sim-principal-upper-set-element-Large-Poset
```

## Properties

### The principal upper sets `↑{x}` and `↑{y}` have the same elements if and only if `x` and `y` are similar

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  {l1 l2 : Level} {x : type-Large-Poset P l1} {y : type-Large-Poset P l2}
  where

  sim-has-same-elements-principal-upper-set-element-Large-Poset :
    has-same-elements-Large-Subposet P
      ( principal-upper-set-element-Large-Poset P x)
      ( principal-upper-set-element-Large-Poset P y) →
    sim-Large-Poset P x y
  pr1 (sim-has-same-elements-principal-upper-set-element-Large-Poset H) =
    backward-implication (H y) (refl-leq-Large-Poset P y)
  pr2 (sim-has-same-elements-principal-upper-set-element-Large-Poset H) =
    forward-implication (H x) (refl-leq-Large-Poset P x)

  has-same-elements-principal-upper-set-element-sim-Large-Poset :
    sim-Large-Poset P x y →
    has-same-elements-Large-Subposet P
      ( principal-upper-set-element-Large-Poset P x)
      ( principal-upper-set-element-Large-Poset P y)
  pr1
    ( has-same-elements-principal-upper-set-element-sim-Large-Poset (H , K) z)
    ( p) =
    transitive-leq-Large-Poset P y x z p K
  pr2
    ( has-same-elements-principal-upper-set-element-sim-Large-Poset (H , K) z)
    ( q) =
    transitive-leq-Large-Poset P x y z q H
```

### For two elements `x` and `y` of a large poset of the same universe level, if the principal upper sets `↑{x}` and `↑{y}` have the same elements, then `x` and `y` are equal

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  {l1 : Level} (x y : type-Large-Poset P l1)
  where

  eq-has-same-elements-principal-upper-set-element-Large-Poset :
    has-same-elements-Large-Subposet P
      ( principal-upper-set-element-Large-Poset P x)
      ( principal-upper-set-element-Large-Poset P y) →
    x ＝ y
  eq-has-same-elements-principal-upper-set-element-Large-Poset H =
    antisymmetric-leq-Large-Poset P x y
      ( pr1 (sim-has-same-elements-principal-upper-set-element-Large-Poset P H))
      ( pr2 (sim-has-same-elements-principal-upper-set-element-Large-Poset P H))
```
