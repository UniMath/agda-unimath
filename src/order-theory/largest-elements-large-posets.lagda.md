# Largest elements in large posets

```agda
module order-theory.largest-elements-large-posets where
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

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  where

  record
    has-largest-element-Large-Poset : UUω
    where
    field
      top-has-largest-element-Large-Poset :
        type-Large-Poset P lzero
      is-largest-element-top-has-largest-element-Large-Poset :
        {l1 : Level} (x : type-Large-Poset P l1) →
        leq-Large-Poset P x top-has-largest-element-Large-Poset

  open has-largest-element-Large-Poset public
```

## Properties

### If `P` is a family of large posets, then `Π-Large-Poset P` has a largest element

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {l1 : Level} {I : UU l1} (P : I → Large-Poset α β)
  where

  has-largest-element-Π-Large-Poset :
    ((i : I) → has-largest-element-Large-Poset (P i)) →
    has-largest-element-Large-Poset (Π-Large-Poset P)
  top-has-largest-element-Large-Poset
    ( has-largest-element-Π-Large-Poset H) i =
    top-has-largest-element-Large-Poset (H i)
  is-largest-element-top-has-largest-element-Large-Poset
    ( has-largest-element-Π-Large-Poset H) x i =
    is-largest-element-top-has-largest-element-Large-Poset (H i) (x i)
```
