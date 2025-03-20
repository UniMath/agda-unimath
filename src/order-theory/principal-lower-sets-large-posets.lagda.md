# Principal lower sets of large posets

```agda
open import foundation.function-extensionality-axiom

module
  order-theory.principal-lower-sets-large-posets
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.logical-equivalences funext
open import foundation.universe-levels

open import order-theory.large-posets funext
open import order-theory.large-subposets funext
open import order-theory.large-subpreorders funext
open import order-theory.similarity-of-elements-large-posets funext
```

</details>

## Idea

The **principal lower set** `↓{x}` of an element `x` of a
[large poset](order-theory.large-posets.md) `P` is the
[large subposet](order-theory.large-subposets.md) consisting of all elements
`y ≤ x` in `P`.

Two elements `x` and `y` in a large poset `P` are
[similar](order-theory.similarity-of-elements-large-posets.md) if and only if
they have the same principal lower sets, and if `x` and `y` are of the same
[universe level](foundation.universe-levels.md), then `x` and `y` are equal if
and only if they have the same principal lower sets. To see this, note that if
`↓{x} = ↓{y}`, then we have the implications `(x ≤ x) → (x ≤ y)` and
`(y ≤ y) → (y ≤ x)`.

## Definitions

### The predicate of being a principal lower set of an element

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  {l1 : Level} (x : type-Large-Poset P l1)
  {γ : Level → Level} (S : Large-Subposet γ P)
  where

  is-principal-lower-set-Large-Subposet : UUω
  is-principal-lower-set-Large-Subposet =
    {l : Level} (y : type-Large-Poset P l) →
    leq-Large-Poset P y x ↔ is-in-Large-Subposet P S y
```

### The principal lower set of an element

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  {l1 : Level} (x : type-Large-Poset P l1)
  where

  large-subpreorder-principal-lower-set-element-Large-Poset :
    Large-Subpreorder (λ l → β l l1) (large-preorder-Large-Poset P)
  large-subpreorder-principal-lower-set-element-Large-Poset y =
    leq-prop-Large-Poset P y x

  is-closed-under-sim-principal-lower-set-element-Large-Poset :
    is-closed-under-sim-Large-Subpreorder P
      ( large-subpreorder-principal-lower-set-element-Large-Poset)
  is-closed-under-sim-principal-lower-set-element-Large-Poset y z p q l =
    transitive-leq-Large-Poset P z y x l q

  principal-lower-set-element-Large-Poset : Large-Subposet (λ l → β l l1) P
  large-subpreorder-Large-Subposet principal-lower-set-element-Large-Poset =
    large-subpreorder-principal-lower-set-element-Large-Poset
  is-closed-under-sim-Large-Subposet principal-lower-set-element-Large-Poset =
    is-closed-under-sim-principal-lower-set-element-Large-Poset
```

## Properties

### The principal lower sets `↓{x}` and `↓{y}` have the same elements if and only if `x` and `y` are similar

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  {l1 l2 : Level} {x : type-Large-Poset P l1} {y : type-Large-Poset P l2}
  where

  sim-has-same-elements-principal-lower-set-element-Large-Poset :
    has-same-elements-Large-Subposet P
      ( principal-lower-set-element-Large-Poset P x)
      ( principal-lower-set-element-Large-Poset P y) →
    sim-Large-Poset P x y
  pr1 (sim-has-same-elements-principal-lower-set-element-Large-Poset H) =
    forward-implication (H x) (refl-leq-Large-Poset P x)
  pr2 (sim-has-same-elements-principal-lower-set-element-Large-Poset H) =
    backward-implication (H y) (refl-leq-Large-Poset P y)

  has-same-elements-principal-lower-set-element-sim-Large-Poset :
    sim-Large-Poset P x y →
    has-same-elements-Large-Subposet P
      ( principal-lower-set-element-Large-Poset P x)
      ( principal-lower-set-element-Large-Poset P y)
  pr1
    ( has-same-elements-principal-lower-set-element-sim-Large-Poset (H , K) z) =
    transitive-leq-Large-Poset P z x y H
  pr2
    ( has-same-elements-principal-lower-set-element-sim-Large-Poset (H , K) z) =
    transitive-leq-Large-Poset P z y x K
```

### For two elements `x` and `y` of a large poset of the same universe level, if the principal lower sets `↓{x}` and `↓{y}` have the same elements, then `x` and `y` are equal

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  {l1 : Level} (x y : type-Large-Poset P l1)
  where

  eq-has-same-elements-principal-lower-set-element-Large-Poset :
    has-same-elements-Large-Subposet P
      ( principal-lower-set-element-Large-Poset P x)
      ( principal-lower-set-element-Large-Poset P y) →
    x ＝ y
  eq-has-same-elements-principal-lower-set-element-Large-Poset H =
    antisymmetric-leq-Large-Poset P x y
      ( pr1 (sim-has-same-elements-principal-lower-set-element-Large-Poset P H))
      ( pr2 (sim-has-same-elements-principal-lower-set-element-Large-Poset P H))
```
