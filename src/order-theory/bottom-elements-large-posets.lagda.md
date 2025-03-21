# Bottom elements in large posets

```agda
module order-theory.bottom-elements-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import order-theory.dependent-products-large-posets
open import order-theory.large-posets
```

</details>

## Idea

We say that a [large poset](order-theory.large-posets.md) `P` has a
{{#concept "least element" Disambiguation="in a large poset" Agda=is-bottom-element-Large-Poset}}
if it comes equipped with an element `t : type-Large-Poset P lzero` such that
`t ≤ x` holds for every `x : P`.

## Definition

### The predicate on elements of posets of being a bottom element

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  is-bottom-element-Large-Poset :
    {l1 : Level} → type-Large-Poset P l1 → UUω
  is-bottom-element-Large-Poset x =
    {l : Level} (y : type-Large-Poset P l) → leq-Large-Poset P x y
```

### The predicate on posets of having a bottom element

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  where

  record
    has-bottom-element-Large-Poset : UUω
    where
    field
      bottom-has-bottom-element-Large-Poset :
        type-Large-Poset P lzero
      is-bottom-element-bottom-has-bottom-element-Large-Poset :
        is-bottom-element-Large-Poset P bottom-has-bottom-element-Large-Poset

  open has-bottom-element-Large-Poset public
```

## Properties

### If `P` is a family of large posets, then `Π-Large-Poset P` has a bottom element

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {l1 : Level} {I : UU l1} (P : I → Large-Poset α β)
  where

  has-bottom-element-Π-Large-Poset :
    ((i : I) → has-bottom-element-Large-Poset (P i)) →
    has-bottom-element-Large-Poset (Π-Large-Poset P)
  bottom-has-bottom-element-Large-Poset
    ( has-bottom-element-Π-Large-Poset H) i =
    bottom-has-bottom-element-Large-Poset (H i)
  is-bottom-element-bottom-has-bottom-element-Large-Poset
    ( has-bottom-element-Π-Large-Poset H) x i =
    is-bottom-element-bottom-has-bottom-element-Large-Poset (H i) (x i)
```
