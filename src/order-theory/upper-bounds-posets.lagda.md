# Upper bounds in posets

```agda
module order-theory.upper-bounds-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
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
    product-Prop (leq-prop-Poset P x z) (leq-prop-Poset P y z)

  is-binary-upper-bound-Poset :
    (x y z : type-Poset P) → UU l2
  is-binary-upper-bound-Poset x y z =
    type-Prop (is-binary-upper-bound-Poset-Prop x y z)

  is-prop-is-binary-upper-bound-Poset :
    (x y z : type-Poset P) → is-prop (is-binary-upper-bound-Poset x y z)
  is-prop-is-binary-upper-bound-Poset x y z =
    is-prop-type-Prop (is-binary-upper-bound-Poset-Prop x y z)

module _
  {l1 l2 : Level} (P : Poset l1 l2) {a b x : type-Poset P}
  (H : is-binary-upper-bound-Poset P a b x)
  where

  leq-left-is-binary-upper-bound-Poset : leq-Poset P a x
  leq-left-is-binary-upper-bound-Poset = pr1 H

  leq-right-is-binary-upper-bound-Poset : leq-Poset P b x
  leq-right-is-binary-upper-bound-Poset = pr2 H
```

### Upper bounds of families of elements

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-upper-bound-family-of-elements-prop-Poset :
    {l : Level} {I : UU l} → (I → type-Poset P) → type-Poset P →
    Prop (l2 ⊔ l)
  is-upper-bound-family-of-elements-prop-Poset {l} {I} f z =
    Π-Prop I (λ i → leq-prop-Poset P (f i) z)

  is-upper-bound-family-of-elements-Poset :
    {l : Level} {I : UU l} → (I → type-Poset P) → type-Poset P →
    UU (l2 ⊔ l)
  is-upper-bound-family-of-elements-Poset f z =
    type-Prop (is-upper-bound-family-of-elements-prop-Poset f z)

  is-prop-is-upper-bound-family-of-elements-Poset :
    {l : Level} {I : UU l} (f : I → type-Poset P) (z : type-Poset P) →
    is-prop (is-upper-bound-family-of-elements-Poset f z)
  is-prop-is-upper-bound-family-of-elements-Poset f z =
    is-prop-type-Prop (is-upper-bound-family-of-elements-prop-Poset f z)
```

## Properties

### Any element greater than an upper bound of `a` and `b` is an upper bound of `a` and `b`

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) {a b x : type-Poset P}
  (H : is-binary-upper-bound-Poset P a b x)
  where

  is-binary-upper-bound-leq-Poset :
    {y : type-Poset P} →
    leq-Poset P x y → is-binary-upper-bound-Poset P a b y
  pr1 (is-binary-upper-bound-leq-Poset K) =
    transitive-leq-Poset P a x _
      ( K)
      ( leq-left-is-binary-upper-bound-Poset P H)
  pr2 (is-binary-upper-bound-leq-Poset K) =
    transitive-leq-Poset P b x _
      ( K)
      ( leq-right-is-binary-upper-bound-Poset P H)
```

### Any element greater than an upper bound of a family of elements `a` is an upper bound of `a`

```agda
module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) {I : UU l3} {a : I → type-Poset P}
  {x : type-Poset P} (H : is-upper-bound-family-of-elements-Poset P a x)
  where

  is-upper-bound-family-of-elements-leq-Poset :
    {y : type-Poset P} → leq-Poset P x y →
    is-upper-bound-family-of-elements-Poset P a y
  is-upper-bound-family-of-elements-leq-Poset K i =
    transitive-leq-Poset P (a i) x _ K (H i)
```
