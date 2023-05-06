# Lower bounds in posets

```agda
module order-theory.lower-bounds-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.posets
```

</details>

## Idea

A **lower bound** of two elements `x` and `y` in a poset `P` is an element `z`
such that both `z ≤ x` and `z ≤ y` hold. Similarly, a **lower bound** of a
family `x : I → P` of elements in `P` is an element `z` such that `z ≤ x i`
holds for every `i : I`.

## Definitions

### Binary lower bounds

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-binary-lower-bound-Poset-Prop :
    (x y z : type-Poset P) → Prop l2
  is-binary-lower-bound-Poset-Prop x y z =
    prod-Prop (leq-Poset-Prop P z x) (leq-Poset-Prop P z y)

  is-binary-lower-bound-Poset :
    (x y z : type-Poset P) → UU l2
  is-binary-lower-bound-Poset x y z =
    type-Prop (is-binary-lower-bound-Poset-Prop x y z)

  is-prop-is-binary-lower-bound-Poset :
    (x y z : type-Poset P) → is-prop (is-binary-lower-bound-Poset x y z)
  is-prop-is-binary-lower-bound-Poset x y z =
    is-prop-type-Prop (is-binary-lower-bound-Poset-Prop x y z)
```

### Lower bounds of families of elements

```agda
module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) {I : UU l3} (x : I → type-Poset P)
  where

  is-lower-bound-family-of-elements-Poset-Prop : type-Poset P → Prop (l2 ⊔ l3)
  is-lower-bound-family-of-elements-Poset-Prop z =
    Π-Prop I (λ i → leq-Poset-Prop P z (x i))

  is-lower-bound-family-of-elements-Poset : type-Poset P → UU (l2 ⊔ l3)
  is-lower-bound-family-of-elements-Poset z =
    type-Prop (is-lower-bound-family-of-elements-Poset-Prop z)

  is-prop-is-lower-bound-family-of-elements-Poset :
    (z : type-Poset P) → is-prop (is-lower-bound-family-of-elements-Poset z)
  is-prop-is-lower-bound-family-of-elements-Poset z =
    is-prop-type-Prop (is-lower-bound-family-of-elements-Poset-Prop z)
```
