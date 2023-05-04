# Least upper bounds in posets

```agda
module order-theory.least-upper-bounds-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.upper-bounds-posets
```

</details>

## Idea

An **upper bound** of two elements `x` and `y` in a poset `P` is an element `z`
such that both `x ≤ z` and `y ≤ z` hold. A **least upper bound** of `x` and `y`
is an upper bound `z` of `x` and `y` such that `z ≤ w` holds for any upper bound
`w` of `x` and `y`.

## Definitions

### Lower bounds of pairs of elements in a poset

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-least-binary-upper-bound-Poset-Prop :
    (x y z : element-Poset P) → Prop (l1 ⊔ l2)
  is-least-binary-upper-bound-Poset-Prop x y z =
    prod-Prop
      ( is-binary-upper-bound-Poset-Prop P x y z)
      ( Π-Prop
        ( element-Poset P)
        ( λ w →
          function-Prop
            ( is-binary-upper-bound-Poset P x y w)
            ( leq-Poset-Prop P z w)))

  is-least-binary-upper-bound-Poset :
    (x y z : element-Poset P) → UU (l1 ⊔ l2)
  is-least-binary-upper-bound-Poset x y z =
    type-Prop (is-least-binary-upper-bound-Poset-Prop x y z)

  is-prop-is-least-binary-upper-bound-Poset :
    (x y z : element-Poset P) →
    is-prop (is-least-binary-upper-bound-Poset x y z)
  is-prop-is-least-binary-upper-bound-Poset x y z =
    is-prop-type-Prop (is-least-binary-upper-bound-Poset-Prop x y z)

  has-least-binary-upper-bound-Poset :
    (x y : element-Poset P) → UU (l1 ⊔ l2)
  has-least-binary-upper-bound-Poset x y =
    Σ (element-Poset P) (is-least-binary-upper-bound-Poset x y)

  all-elements-equal-has-least-binary-upper-bound-Poset :
    (x y : element-Poset P) →
    all-elements-equal (has-least-binary-upper-bound-Poset x y)
  all-elements-equal-has-least-binary-upper-bound-Poset x y
    (pair u H) (pair v K) =
    eq-type-subtype
      ( is-least-binary-upper-bound-Poset-Prop x y)
      ( antisymmetric-leq-Poset P u v
        ( pr2 H v (pr1 K))
        ( pr2 K u (pr1 H)))

  is-prop-has-least-binary-upper-bound-Poset :
    (x y : element-Poset P) → is-prop (has-least-binary-upper-bound-Poset x y)
  is-prop-has-least-binary-upper-bound-Poset x y =
    is-prop-all-elements-equal
      ( all-elements-equal-has-least-binary-upper-bound-Poset x y)

  has-least-binary-upper-bound-Poset-Prop :
    (x y : element-Poset P) → Prop (l1 ⊔ l2)
  pr1 (has-least-binary-upper-bound-Poset-Prop x y) =
    has-least-binary-upper-bound-Poset x y
  pr2 (has-least-binary-upper-bound-Poset-Prop x y) =
    is-prop-has-least-binary-upper-bound-Poset x y
```

### Least upper bounds of families of elements

```agda
module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) {I : UU l3} (x : I → element-Poset P)
  where

  is-least-upper-bound-family-of-elements-Poset-Prop :
    element-Poset P → Prop (l1 ⊔ l2 ⊔ l3)
  is-least-upper-bound-family-of-elements-Poset-Prop z =
    prod-Prop
      ( is-upper-bound-family-of-elements-Poset-Prop P x z)
      ( Π-Prop
        ( element-Poset P)
        ( λ w →
          function-Prop
            ( is-upper-bound-family-of-elements-Poset P x w)
            ( leq-Poset-Prop P z w)))

  is-least-upper-bound-family-of-elements-Poset :
    element-Poset P → UU (l1 ⊔ l2 ⊔ l3)
  is-least-upper-bound-family-of-elements-Poset z =
    type-Prop (is-least-upper-bound-family-of-elements-Poset-Prop z)

  is-prop-is-least-upper-bound-family-of-elements-Poset :
    (z : element-Poset P) →
    is-prop (is-least-upper-bound-family-of-elements-Poset z)
  is-prop-is-least-upper-bound-family-of-elements-Poset z =
    is-prop-type-Prop (is-least-upper-bound-family-of-elements-Poset-Prop z)

  has-least-upper-bound-family-of-elements-Poset : UU (l1 ⊔ l2 ⊔ l3)
  has-least-upper-bound-family-of-elements-Poset =
    Σ (element-Poset P) is-least-upper-bound-family-of-elements-Poset

  all-elements-equal-has-least-upper-bound-family-of-elements-Poset :
    all-elements-equal has-least-upper-bound-family-of-elements-Poset
  all-elements-equal-has-least-upper-bound-family-of-elements-Poset
    (pair u H) (pair v K) =
    eq-type-subtype
      ( is-least-upper-bound-family-of-elements-Poset-Prop)
      ( antisymmetric-leq-Poset P u v
        ( pr2 H v (pr1 K))
        ( pr2 K u (pr1 H)))

  is-prop-has-least-upper-bound-family-of-elements-Poset :
    is-prop has-least-upper-bound-family-of-elements-Poset
  is-prop-has-least-upper-bound-family-of-elements-Poset =
    is-prop-all-elements-equal
      all-elements-equal-has-least-upper-bound-family-of-elements-Poset

  has-least-upper-bound-family-of-elements-Poset-Prop : Prop (l1 ⊔ l2 ⊔ l3)
  pr1 has-least-upper-bound-family-of-elements-Poset-Prop =
    has-least-upper-bound-family-of-elements-Poset
  pr2 has-least-upper-bound-family-of-elements-Poset-Prop =
    is-prop-has-least-upper-bound-family-of-elements-Poset
```
