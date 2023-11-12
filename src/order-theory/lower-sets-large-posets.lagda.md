# Lower sets of large posets

```agda
module order-theory.lower-sets-large-posets where
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

The **lower set** of an element `x` of a
[large poset](order-theory.large-posets.md) `P` is the
[large subposet](order-theory.large-subposets.md) consisting of all elements
`y ≤ x` in `P`. The lower set of `x` is often denoted by `↓(x)`.

Two elements `x` and `y` in a large poset `P` are
[similar](order-theory.similarity-of-elements-large-posets.md) if and only if
they have the same lower sets, and if `x` and `y` are of the same
[universe level](foundation.universe-levels.md), then `x` and `y` are equal if
and only if they have the same lower sets. To see this, simply note that if
`↓(x) = ↓(y)`, then we have the implications `(x ≤ x) → (x ≤ y)` and
`(y ≤ y) → (y ≤ x)`.

## Definitions

### The predicate of being a lower set of an element

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  {l1 : Level} (x : type-Large-Poset P l1)
  {γ : Level → Level} (S : Large-Subposet γ P)
  where

  is-lower-set-Large-Subposet : UUω
  is-lower-set-Large-Subposet =
    {l : Level} (y : type-Large-Poset P l) →
    leq-Large-Poset P y x ↔ is-in-Large-Subposet P S y
```

### The lower set of an element

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  {l1 : Level} (x : type-Large-Poset P l1)
  where

  large-subpreorder-lower-set-element-Large-Poset :
    Large-Subpreorder (λ l → β l l1) (large-preorder-Large-Poset P)
  large-subpreorder-lower-set-element-Large-Poset y = leq-prop-Large-Poset P y x

  is-closed-under-sim-lower-set-element-Large-Poset :
    is-closed-under-sim-Large-Subpreorder P
      ( large-subpreorder-lower-set-element-Large-Poset)
  is-closed-under-sim-lower-set-element-Large-Poset y z p q l =
    transitive-leq-Large-Poset P z y x l q

  lower-set-element-Large-Poset : Large-Subposet (λ l → β l l1) P
  large-subpreorder-Large-Subposet lower-set-element-Large-Poset =
    large-subpreorder-lower-set-element-Large-Poset
  is-closed-under-sim-Large-Subposet lower-set-element-Large-Poset =
    is-closed-under-sim-lower-set-element-Large-Poset
```

## Properties

### The lower sets `↓(x)` and `↓(y)` have the same elements if and only if `x` and `y` are similar

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  {l1 l2 : Level} {x : type-Large-Poset P l1} {y : type-Large-Poset P l2}
  where

  sim-has-same-elements-lower-set-element-Large-Poset :
    has-same-elements-Large-Subposet P
      ( lower-set-element-Large-Poset P x)
      ( lower-set-element-Large-Poset P y) →
    sim-Large-Poset P x y
  pr1 (sim-has-same-elements-lower-set-element-Large-Poset H) =
    forward-implication (H x) (refl-leq-Large-Poset P x)
  pr2 (sim-has-same-elements-lower-set-element-Large-Poset H) =
    backward-implication (H y) (refl-leq-Large-Poset P y)

  has-same-elements-lower-set-element-sim-Large-Poset :
    sim-Large-Poset P x y →
    has-same-elements-Large-Subposet P
      ( lower-set-element-Large-Poset P x)
      ( lower-set-element-Large-Poset P y)
  pr1 (has-same-elements-lower-set-element-sim-Large-Poset (H , K) z) p =
    transitive-leq-Large-Poset P z x y H p
  pr2 (has-same-elements-lower-set-element-sim-Large-Poset (H , K) z) q =
    transitive-leq-Large-Poset P z y x K q
```

### For two elements `x` and `y` of a large poset the same universe level, if the lower sets `↓(x)` and `↓(y)` have the same elements, then `x` and `y` are equal

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  {l1 : Level} (x y : type-Large-Poset P l1)
  where

  eq-has-same-elements-lower-set-element-Large-Poset :
    has-same-elements-Large-Subposet P
      ( lower-set-element-Large-Poset P x)
      ( lower-set-element-Large-Poset P y) →
    x ＝ y
  eq-has-same-elements-lower-set-element-Large-Poset H =
    antisymmetric-leq-Large-Poset P x y
      ( pr1 (sim-has-same-elements-lower-set-element-Large-Poset P H))
      ( pr2 (sim-has-same-elements-lower-set-element-Large-Poset P H))
```
