# Greatest lower bounds in posets

```agda
module order-theory.greatest-lower-bounds-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.lower-bounds-posets
open import order-theory.posets
```

</details>

## Idea

A **greatest lower bound** of `x` and `y` is a lower bound `z` of `x` and `y`
such that `w ≤ z` holds for any lower bound of `x` and `y`. Similarly, a
**greatest lower bound** of a family `x : I → P` of elements of `P` is a lower
bound `z` of `x` such that `w ≤ z` holds for any lower bound of `x`.

## Definitions

### Lower bounds of pairs of elements in a poset

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-greatest-binary-lower-bound-Poset-Prop :
    (x y z : type-Poset P) → Prop (l1 ⊔ l2)
  is-greatest-binary-lower-bound-Poset-Prop x y z =
    prod-Prop
      ( is-binary-lower-bound-Poset-Prop P x y z)
      ( Π-Prop
        ( type-Poset P)
        ( λ w →
          function-Prop
            ( is-binary-lower-bound-Poset P x y w)
            ( leq-Poset-Prop P w z)))

  is-greatest-binary-lower-bound-Poset :
    (x y z : type-Poset P) → UU (l1 ⊔ l2)
  is-greatest-binary-lower-bound-Poset x y z =
    type-Prop (is-greatest-binary-lower-bound-Poset-Prop x y z)

  is-prop-is-greatest-binary-lower-bound-Poset :
    (x y z : type-Poset P) →
    is-prop (is-greatest-binary-lower-bound-Poset x y z)
  is-prop-is-greatest-binary-lower-bound-Poset x y z =
    is-prop-type-Prop (is-greatest-binary-lower-bound-Poset-Prop x y z)

  has-greatest-binary-lower-bound-Poset :
    (x y : type-Poset P) → UU (l1 ⊔ l2)
  has-greatest-binary-lower-bound-Poset x y =
    Σ (type-Poset P) (is-greatest-binary-lower-bound-Poset x y)

  all-types-equal-has-greatest-binary-lower-bound-Poset :
    (x y : type-Poset P) →
    all-elements-equal (has-greatest-binary-lower-bound-Poset x y)
  all-types-equal-has-greatest-binary-lower-bound-Poset x y
    (pair u H) (pair v K) =
    eq-type-subtype
      ( is-greatest-binary-lower-bound-Poset-Prop x y)
      ( antisymmetric-leq-Poset P u v
        ( pr2 K u (pr1 H))
        ( pr2 H v (pr1 K)))

  is-prop-has-greatest-binary-lower-bound-Poset :
    (x y : type-Poset P) →
    is-prop (has-greatest-binary-lower-bound-Poset x y)
  is-prop-has-greatest-binary-lower-bound-Poset x y =
    is-prop-all-elements-equal
      ( all-types-equal-has-greatest-binary-lower-bound-Poset x y)

  has-greatest-binary-lower-bound-Poset-Prop :
    (x y : type-Poset P) → Prop (l1 ⊔ l2)
  pr1 (has-greatest-binary-lower-bound-Poset-Prop x y) =
    has-greatest-binary-lower-bound-Poset x y
  pr2 (has-greatest-binary-lower-bound-Poset-Prop x y) =
    is-prop-has-greatest-binary-lower-bound-Poset x y
```

### Greatest lower bounds of families of elements

```agda
module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) {I : UU l3} (x : I → type-Poset P)
  where

  is-greatest-lower-bound-family-of-elements-Poset-Prop :
    type-Poset P → Prop (l1 ⊔ l2 ⊔ l3)
  is-greatest-lower-bound-family-of-elements-Poset-Prop z =
    prod-Prop
      ( is-lower-bound-family-of-elements-Poset-Prop P x z)
      ( Π-Prop
        ( type-Poset P)
        ( λ w →
          function-Prop
            ( is-lower-bound-family-of-elements-Poset P x w)
            ( leq-Poset-Prop P w z)))

  is-greatest-lower-bound-family-of-elements-Poset :
    type-Poset P → UU (l1 ⊔ l2 ⊔ l3)
  is-greatest-lower-bound-family-of-elements-Poset z =
    type-Prop (is-greatest-lower-bound-family-of-elements-Poset-Prop z)

  is-prop-is-greatest-lower-bound-family-of-elements-Poset :
    (z : type-Poset P) →
    is-prop (is-greatest-lower-bound-family-of-elements-Poset z)
  is-prop-is-greatest-lower-bound-family-of-elements-Poset z =
    is-prop-type-Prop (is-greatest-lower-bound-family-of-elements-Poset-Prop z)

  has-greatest-lower-bound-family-of-elements-Poset : UU (l1 ⊔ l2 ⊔ l3)
  has-greatest-lower-bound-family-of-elements-Poset =
    Σ (type-Poset P) is-greatest-lower-bound-family-of-elements-Poset

  all-elements-equal-has-greatest-lower-bound-family-of-elements-Poset :
    all-elements-equal has-greatest-lower-bound-family-of-elements-Poset
  all-elements-equal-has-greatest-lower-bound-family-of-elements-Poset
    ( z , (H1 , H2)) (w , (K1 , K2)) =
    eq-type-subtype
      ( is-greatest-lower-bound-family-of-elements-Poset-Prop)
      ( antisymmetric-leq-Poset P z w (K2 z H1) (H2 w K1))

  is-prop-has-greatest-lower-bound-family-of-elements-Poset :
    is-prop has-greatest-lower-bound-family-of-elements-Poset
  is-prop-has-greatest-lower-bound-family-of-elements-Poset =
    is-prop-all-elements-equal
      all-elements-equal-has-greatest-lower-bound-family-of-elements-Poset

  has-greatest-lower-bound-family-of-elements-Poset-Prop : Prop (l1 ⊔ l2 ⊔ l3)
  pr1 has-greatest-lower-bound-family-of-elements-Poset-Prop =
    has-greatest-lower-bound-family-of-elements-Poset
  pr2 has-greatest-lower-bound-family-of-elements-Poset-Prop =
    is-prop-has-greatest-lower-bound-family-of-elements-Poset
```
