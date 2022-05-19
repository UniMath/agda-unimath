# Least upper bounds in posets

```agda
{-# OPTIONS --without-K --exact-split #-}

module order-theory.least-upper-bounds-posets where

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.propositions using
  ( UU-Prop; is-prop; type-Prop; is-prop-type-Prop; all-elements-equal;
    is-prop-all-elements-equal; prod-Prop; Π-Prop; function-Prop)
open import foundation.subtypes using (eq-subtype)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import order-theory.posets using
  ( Poset; element-Poset; leq-poset-Prop; antisymmetric-leq-Poset)
```

## Idea

An upper bound of two elements `x` and `y` in a poset `P` is an element `z` such that both `x ≤ z` and `y ≤ z` hold. A least upper bound of `x` and `y` is an upper bound `z` of `x` and `y` such that `z ≤ w` holds for any upper bound `w` of `x` and `y`.

## Definitions

### Lower bounds of pairs of elements in a poset

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-binary-upper-bound-poset-Prop :
    (x y z : element-Poset P) → UU-Prop l2
  is-binary-upper-bound-poset-Prop x y z =
    prod-Prop (leq-poset-Prop P x z) (leq-poset-Prop P y z)

  is-binary-upper-bound-Poset :
    (x y z : element-Poset P) → UU l2
  is-binary-upper-bound-Poset x y z = type-Prop (is-binary-upper-bound-poset-Prop x y z)

  is-prop-is-binary-upper-bound-Poset :
    (x y z : element-Poset P) → is-prop (is-binary-upper-bound-Poset x y z)
  is-prop-is-binary-upper-bound-Poset x y z =
    is-prop-type-Prop (is-binary-upper-bound-poset-Prop x y z)

  is-least-binary-upper-bound-poset-Prop :
    (x y z : element-Poset P) → UU-Prop (l1 ⊔ l2)
  is-least-binary-upper-bound-poset-Prop x y z =
    prod-Prop
      ( is-binary-upper-bound-poset-Prop x y z)
      ( Π-Prop
        ( element-Poset P)
        ( λ w →
          function-Prop
            ( is-binary-upper-bound-Poset x y w)
            ( leq-poset-Prop P z w)))

  is-least-binary-upper-bound-Poset :
    (x y z : element-Poset P) → UU (l1 ⊔ l2)
  is-least-binary-upper-bound-Poset x y z =
    type-Prop (is-least-binary-upper-bound-poset-Prop x y z)

  is-prop-is-least-binary-upper-bound-Poset :
    (x y z : element-Poset P) → is-prop (is-least-binary-upper-bound-Poset x y z)
  is-prop-is-least-binary-upper-bound-Poset x y z =
    is-prop-type-Prop (is-least-binary-upper-bound-poset-Prop x y z)

  has-least-binary-upper-bound-Poset :
    (x y : element-Poset P) → UU (l1 ⊔ l2)
  has-least-binary-upper-bound-Poset x y =
    Σ (element-Poset P) (is-least-binary-upper-bound-Poset x y)

  all-elements-equal-has-least-binary-upper-bound-Poset :
    (x y : element-Poset P) →
    all-elements-equal (has-least-binary-upper-bound-Poset x y)
  all-elements-equal-has-least-binary-upper-bound-Poset x y (pair u H) (pair v K) =
    eq-subtype
      ( is-least-binary-upper-bound-poset-Prop x y)
      ( antisymmetric-leq-Poset P u v
        ( pr2 H v (pr1 K))
        ( pr2 K u (pr1 H)))

  is-prop-has-least-binary-upper-bound-Poset :
    (x y : element-Poset P) → is-prop (has-least-binary-upper-bound-Poset x y)
  is-prop-has-least-binary-upper-bound-Poset x y =
    is-prop-all-elements-equal
      ( all-elements-equal-has-least-binary-upper-bound-Poset x y)

  has-least-binary-upper-bound-poset-Prop :
    (x y : element-Poset P) → UU-Prop (l1 ⊔ l2)
  pr1 (has-least-binary-upper-bound-poset-Prop x y) =
    has-least-binary-upper-bound-Poset x y
  pr2 (has-least-binary-upper-bound-poset-Prop x y) =
    is-prop-has-least-binary-upper-bound-Poset x y
```
