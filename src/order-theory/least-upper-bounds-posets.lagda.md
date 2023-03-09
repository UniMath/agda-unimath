# Least upper bounds in posets

```agda
module order-theory.least-upper-bounds-posets where
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

An upper bound of two elements `x` and `y` in a poset `P` is an element `z` such that both `x ≤ z` and `y ≤ z` hold. A least upper bound of `x` and `y` is an upper bound `z` of `x` and `y` such that `z ≤ w` holds for any upper bound `w` of `x` and `y`.

## Definitions

### Lower bounds of pairs of elements in a poset

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-binary-upper-bound-poset-Prop :
    (x y z : element-Poset P) → Prop l2
  is-binary-upper-bound-poset-Prop x y z =
    prod-Prop (leq-poset-Prop P x z) (leq-poset-Prop P y z)

  is-binary-upper-bound-Poset :
    (x y z : element-Poset P) → UU l2
  is-binary-upper-bound-Poset x y z =
    type-Prop (is-binary-upper-bound-poset-Prop x y z)

  is-prop-is-binary-upper-bound-Poset :
    (x y z : element-Poset P) → is-prop (is-binary-upper-bound-Poset x y z)
  is-prop-is-binary-upper-bound-Poset x y z =
    is-prop-type-Prop (is-binary-upper-bound-poset-Prop x y z)

  is-least-binary-upper-bound-poset-Prop :
    (x y z : element-Poset P) → Prop (l1 ⊔ l2)
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
  all-elements-equal-has-least-binary-upper-bound-Poset x y
    (pair u H) (pair v K) =
    eq-type-subtype
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
    (x y : element-Poset P) → Prop (l1 ⊔ l2)
  pr1 (has-least-binary-upper-bound-poset-Prop x y) =
    has-least-binary-upper-bound-Poset x y
  pr2 (has-least-binary-upper-bound-poset-Prop x y) =
    is-prop-has-least-binary-upper-bound-Poset x y
```

### Least upper bounds of families of elements

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-upper-bound-family-poset-Prop :
    {l : Level} {I : UU l} → (I → element-Poset P) → element-Poset P →
    Prop (l2 ⊔ l)
  is-upper-bound-family-poset-Prop {l} {I} f z =
    Π-Prop I (λ i → leq-poset-Prop P (f i) z)

  is-upper-bound-family-Poset :
    {l : Level} {I : UU l} → (I → element-Poset P) → element-Poset P →
    UU (l2 ⊔ l)
  is-upper-bound-family-Poset f z =
    type-Prop (is-upper-bound-family-poset-Prop f z)

  is-prop-is-upper-bound-family-Poset :
    {l : Level} {I : UU l} (f : I → element-Poset P) (z : element-Poset P) →
    is-prop (is-upper-bound-family-Poset f z)
  is-prop-is-upper-bound-family-Poset f z =
    is-prop-type-Prop (is-upper-bound-family-poset-Prop f z)

  is-least-upper-bound-family-poset-Prop :
    {l : Level} {I : UU l} (f : I → element-Poset P) (z : element-Poset P) →
    Prop (l1 ⊔ l2 ⊔ l)
  is-least-upper-bound-family-poset-Prop f z =
    prod-Prop
      ( is-upper-bound-family-poset-Prop f z)
      ( Π-Prop
        ( element-Poset P)
        ( λ w →
          function-Prop
            ( is-upper-bound-family-Poset f w)
            ( leq-poset-Prop P z w)))

  is-least-upper-bound-family-Poset :
    {l : Level} {I : UU l} (f : I → element-Poset P) (z : element-Poset P) →
    UU (l1 ⊔ l2 ⊔ l)
  is-least-upper-bound-family-Poset f z =
    type-Prop (is-least-upper-bound-family-poset-Prop f z)

  is-prop-is-least-upper-bound-family-Poset :
    {l : Level} {I : UU l} (f : I → element-Poset P) (z : element-Poset P) →
    is-prop (is-least-upper-bound-family-Poset f z)
  is-prop-is-least-upper-bound-family-Poset f z =
    is-prop-type-Prop (is-least-upper-bound-family-poset-Prop f z)

  has-least-upper-bound-family-Poset :
    {l : Level} {I : UU l} (f : I → element-Poset P) → UU (l1 ⊔ l2 ⊔ l)
  has-least-upper-bound-family-Poset f =
    Σ (element-Poset P) (is-least-upper-bound-family-Poset f)

  all-elements-equal-has-least-upper-bound-family-Poset :
    {l : Level} {I : UU l} (f : I → element-Poset P) →
    all-elements-equal (has-least-upper-bound-family-Poset f)
  all-elements-equal-has-least-upper-bound-family-Poset f
    (pair u H) (pair v K) =
    eq-type-subtype
      ( is-least-upper-bound-family-poset-Prop f)
      ( antisymmetric-leq-Poset P u v
        ( pr2 H v (pr1 K))
        ( pr2 K u (pr1 H)))

  is-prop-has-least-upper-bound-family-Poset :
    {l : Level} {I : UU l} (f : I → element-Poset P) →
    is-prop (has-least-upper-bound-family-Poset f)
  is-prop-has-least-upper-bound-family-Poset f =
    is-prop-all-elements-equal
      ( all-elements-equal-has-least-upper-bound-family-Poset f)

  has-least-upper-bound-family-poset-Prop :
    {l : Level} {I : UU l} (f : I → element-Poset P) → Prop (l1 ⊔ l2 ⊔ l)
  pr1 (has-least-upper-bound-family-poset-Prop f) =
    has-least-upper-bound-family-Poset f
  pr2 (has-least-upper-bound-family-poset-Prop f) =
    is-prop-has-least-upper-bound-family-Poset f
```
