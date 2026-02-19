# Bottom elements in large posets

```agda
module order-theory.bottom-elements-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import order-theory.dependent-products-large-posets
open import order-theory.large-posets
open import order-theory.similarity-of-elements-large-posets
```

</details>

## Idea

We say that a [large poset](order-theory.large-posets.md) `P` has a
{{#concept "least element" Disambiguation="in a large poset" Agda=is-bottom-element-Large-Poset}}
if for every universe level `l`, it comes equipped with an element
`t : type-Large-Poset P l` such that `t ≤ x` holds for every `x : P l`.

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
        (l : Level) → type-Large-Poset P l
      is-bottom-element-bottom-has-bottom-element-Large-Poset :
        (l : Level) →
        is-bottom-element-Large-Poset
          ( P)
          ( bottom-has-bottom-element-Large-Poset l)

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
    ( has-bottom-element-Π-Large-Poset H) l i =
    bottom-has-bottom-element-Large-Poset (H i) l
  is-bottom-element-bottom-has-bottom-element-Large-Poset
    ( has-bottom-element-Π-Large-Poset H) x l i =
    is-bottom-element-bottom-has-bottom-element-Large-Poset (H i) x (l i)
```

### The bottom elements at any two universe levels are similar

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  (B : has-bottom-element-Large-Poset P)
  where

  abstract
    sim-bottom-element-Large-Poset :
      (l1 l2 : Level) →
      sim-Large-Poset P
        ( bottom-has-bottom-element-Large-Poset B l1)
        ( bottom-has-bottom-element-Large-Poset B l2)
    sim-bottom-element-Large-Poset l1 l2 =
      ( is-bottom-element-bottom-has-bottom-element-Large-Poset B l1
          ( bottom-has-bottom-element-Large-Poset B l2) ,
        is-bottom-element-bottom-has-bottom-element-Large-Poset B l2
          ( bottom-has-bottom-element-Large-Poset B l1))
```
