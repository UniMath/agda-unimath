# Lower bounds in large posets

```agda
module order-theory.lower-bounds-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.universe-levels

open import order-theory.dependent-products-large-posets
open import order-theory.large-posets
```

</details>

## Idea

A **binary lower bound** of two elements `a` and `b` in a large poset `P` is an
element `x` such that both `x ≤ a` and `x ≤ b` hold. Similarly, a **lower
bound** of a family of elements `a : I → P` in a large poset `P` is an element
`x` such that `x ≤ a i` holds for every `i : I`.

## Definitions

### The predicate that an element of a large poset is a lower bound of two elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  {l1 l2 : Level} (a : type-Large-Poset P l1) (b : type-Large-Poset P l2)
  where

  is-binary-lower-bound-Large-Poset :
    {l3 : Level} → type-Large-Poset P l3 → UU (β l3 l1 ⊔ β l3 l2)
  is-binary-lower-bound-Large-Poset x =
    leq-Large-Poset P x a × leq-Large-Poset P x b
```

## Properties

### An element of a dependent product of large posets is a binary lower bound of two elements if and only if it is a pointwise binary lower bound

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {l : Level} {I : UU l} (P : I → Large-Poset α β)
  {l1 l2 : Level} (x : type-Π-Large-Poset P l1) (y : type-Π-Large-Poset P l2)
  where

  is-binary-lower-bound-Π-Large-Poset :
    {l3 : Level} (z : type-Π-Large-Poset P l3) →
    ((i : I) → is-binary-lower-bound-Large-Poset (P i) (x i) (y i) (z i)) →
    is-binary-lower-bound-Large-Poset (Π-Large-Poset P) x y z
  pr1 (is-binary-lower-bound-Π-Large-Poset z H) i = pr1 (H i)
  pr2 (is-binary-lower-bound-Π-Large-Poset z H) i = pr2 (H i)

  is-binary-lower-bound-is-binary-lower-bound-Π-Large-Poset :
    {l3 : Level} (z : type-Π-Large-Poset P l3) →
    is-binary-lower-bound-Large-Poset (Π-Large-Poset P) x y z →
    (i : I) → is-binary-lower-bound-Large-Poset (P i) (x i) (y i) (z i)
  pr1 (is-binary-lower-bound-is-binary-lower-bound-Π-Large-Poset z H i) =
    pr1 H i
  pr2 (is-binary-lower-bound-is-binary-lower-bound-Π-Large-Poset z H i) =
    pr2 H i

  logical-equivalence-is-binary-lower-bound-Π-Large-Poset :
    {l3 : Level} (z : type-Π-Large-Poset P l3) →
    ((i : I) → is-binary-lower-bound-Large-Poset (P i) (x i) (y i) (z i)) ↔
    is-binary-lower-bound-Large-Poset (Π-Large-Poset P) x y z
  pr1 (logical-equivalence-is-binary-lower-bound-Π-Large-Poset z) =
    is-binary-lower-bound-Π-Large-Poset z
  pr2 (logical-equivalence-is-binary-lower-bound-Π-Large-Poset z) =
    is-binary-lower-bound-is-binary-lower-bound-Π-Large-Poset z
```
