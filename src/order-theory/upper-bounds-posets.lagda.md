# Upper bounds in posets

```agda
module order-theory.upper-bounds-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.posets
```

</details>

## Idea

An **upper bound** of two elements `x` and `y` in a poset `P` is an element `z`
such that both `x ≤ z` and `y ≤ z` hold. Similaryly, an **upper bound** of a
family `x : I → P` of elements in `P` is an element `z` such that `x i ≤ z`
holds for every `i : I`.

## Definitions

### Binary upper bounds

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-binary-upper-bound-Poset-Prop :
    (x y z : type-Poset P) → Prop l2
  is-binary-upper-bound-Poset-Prop x y z =
    prod-Prop (leq-Poset-Prop P x z) (leq-Poset-Prop P y z)

  is-binary-upper-bound-Poset :
    (x y z : type-Poset P) → UU l2
  is-binary-upper-bound-Poset x y z =
    type-Prop (is-binary-upper-bound-Poset-Prop x y z)

  is-prop-is-binary-upper-bound-Poset :
    (x y z : type-Poset P) → is-prop (is-binary-upper-bound-Poset x y z)
  is-prop-is-binary-upper-bound-Poset x y z =
    is-prop-type-Prop (is-binary-upper-bound-Poset-Prop x y z)
```

### Upper bounds of families of types

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-upper-bound-family-of-elements-Poset-Prop :
    {l : Level} {I : UU l} → (I → type-Poset P) → type-Poset P →
    Prop (l2 ⊔ l)
  is-upper-bound-family-of-elements-Poset-Prop {l} {I} f z =
    Π-Prop I (λ i → leq-Poset-Prop P (f i) z)

  is-upper-bound-family-of-elements-Poset :
    {l : Level} {I : UU l} → (I → type-Poset P) → type-Poset P →
    UU (l2 ⊔ l)
  is-upper-bound-family-of-elements-Poset f z =
    type-Prop (is-upper-bound-family-of-elements-Poset-Prop f z)

  is-prop-is-upper-bound-family-of-elements-Poset :
    {l : Level} {I : UU l} (f : I → type-Poset P) (z : type-Poset P) →
    is-prop (is-upper-bound-family-of-elements-Poset f z)
  is-prop-is-upper-bound-family-of-elements-Poset f z =
    is-prop-type-Prop (is-upper-bound-family-of-elements-Poset-Prop f z)
```
