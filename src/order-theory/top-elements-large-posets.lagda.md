# Top elements in large posets

```agda
module order-theory.top-elements-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import order-theory.dependent-products-large-posets
open import order-theory.large-posets
```

</details>

## Idea

We say that a [large poset](order-theory.large-posets.md) `P` has a **largest
element** if it comes equipped with an element `t : type-Large-Poset P lzero`
such that `x ≤ t` holds for every `x : P`

## Definition

### The predicate on elements of posets of being a top element

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  is-top-element-Large-Poset :
    {l1 : Level} → type-Large-Poset P l1 → UUω
  is-top-element-Large-Poset x =
    {l : Level} (y : type-Large-Poset P l) → leq-Large-Poset P y x
```

### The predicate on posets of having a top element

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  where

  record
    has-top-element-Large-Poset : UUω
    where
    field
      top-has-top-element-Large-Poset :
        type-Large-Poset P lzero
      is-top-element-top-has-top-element-Large-Poset :
        is-top-element-Large-Poset P top-has-top-element-Large-Poset

  open has-top-element-Large-Poset public
```

## Properties

### If `P` is a family of large posets, then `Π-Large-Poset P` has a largest element

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {l1 : Level} {I : UU l1} (P : I → Large-Poset α β)
  where

  has-top-element-Π-Large-Poset :
    ((i : I) → has-top-element-Large-Poset (P i)) →
    has-top-element-Large-Poset (Π-Large-Poset P)
  top-has-top-element-Large-Poset
    ( has-top-element-Π-Large-Poset H) i =
    top-has-top-element-Large-Poset (H i)
  is-top-element-top-has-top-element-Large-Poset
    ( has-top-element-Π-Large-Poset H) x i =
    is-top-element-top-has-top-element-Large-Poset (H i) (x i)
```
