# Greatest lower bounds in posets

```agda
module order-theory.greatest-lower-bounds-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.posets
```

</details>

## Idea

A lower bound of two elements `x` and `y` in a poset `P` is an element `z` such that both `z ≤ x` and `z ≤ y` hold. A greatest lower bound of `x` and `y` is a lower bound `z` of `x` and `y` such that `w ≤ z` holds for any lower bound of `x` and `y`.

## Definitions

### Lower bounds of pairs of elements in a poset

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-binary-lower-bound-poset-Prop :
    (x y z : element-Poset P) → Prop l2
  is-binary-lower-bound-poset-Prop x y z =
    prod-Prop (leq-poset-Prop P z x) (leq-poset-Prop P z y)

  is-binary-lower-bound-Poset :
    (x y z : element-Poset P) → UU l2
  is-binary-lower-bound-Poset x y z = type-Prop (is-binary-lower-bound-poset-Prop x y z)

  is-prop-is-binary-lower-bound-Poset :
    (x y z : element-Poset P) → is-prop (is-binary-lower-bound-Poset x y z)
  is-prop-is-binary-lower-bound-Poset x y z =
    is-prop-type-Prop (is-binary-lower-bound-poset-Prop x y z)

  is-greatest-binary-lower-bound-poset-Prop :
    (x y z : element-Poset P) → Prop (l1 ⊔ l2)
  is-greatest-binary-lower-bound-poset-Prop x y z =
    prod-Prop
      ( is-binary-lower-bound-poset-Prop x y z)
      ( Π-Prop
        ( element-Poset P)
        ( λ w →
          function-Prop
            ( is-binary-lower-bound-Poset x y w)
            ( leq-poset-Prop P w z)))

  is-greatest-binary-lower-bound-Poset :
    (x y z : element-Poset P) → UU (l1 ⊔ l2)
  is-greatest-binary-lower-bound-Poset x y z =
    type-Prop (is-greatest-binary-lower-bound-poset-Prop x y z)

  is-prop-is-greatest-binary-lower-bound-Poset :
    (x y z : element-Poset P) →
    is-prop (is-greatest-binary-lower-bound-Poset x y z)
  is-prop-is-greatest-binary-lower-bound-Poset x y z =
    is-prop-type-Prop (is-greatest-binary-lower-bound-poset-Prop x y z)

  has-greatest-binary-lower-bound-Poset :
    (x y : element-Poset P) → UU (l1 ⊔ l2)
  has-greatest-binary-lower-bound-Poset x y =
    Σ (element-Poset P) (is-greatest-binary-lower-bound-Poset x y)

  all-elements-equal-has-greatest-binary-lower-bound-Poset :
    (x y : element-Poset P) →
    all-elements-equal (has-greatest-binary-lower-bound-Poset x y)
  all-elements-equal-has-greatest-binary-lower-bound-Poset x y
    (pair u H) (pair v K) =
    eq-type-subtype
      ( is-greatest-binary-lower-bound-poset-Prop x y)
      ( antisymmetric-leq-Poset P u v
        ( pr2 K u (pr1 H))
        ( pr2 H v (pr1 K)))

  is-prop-has-greatest-binary-lower-bound-Poset :
    (x y : element-Poset P) →
    is-prop (has-greatest-binary-lower-bound-Poset x y)
  is-prop-has-greatest-binary-lower-bound-Poset x y =
    is-prop-all-elements-equal
      ( all-elements-equal-has-greatest-binary-lower-bound-Poset x y)

  has-greatest-binary-lower-bound-poset-Prop :
    (x y : element-Poset P) → Prop (l1 ⊔ l2)
  pr1 (has-greatest-binary-lower-bound-poset-Prop x y) =
    has-greatest-binary-lower-bound-Poset x y
  pr2 (has-greatest-binary-lower-bound-poset-Prop x y) =
    is-prop-has-greatest-binary-lower-bound-Poset x y
```
