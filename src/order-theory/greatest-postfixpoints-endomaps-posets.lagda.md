# Greatest postfixpoints of endomaps on posets

```agda
module order-theory.greatest-postfixpoints-endomaps-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.universe-levels

open import order-theory.least-upper-bounds-postfixpoints-endomaps-posets
open import order-theory.order-preserving-maps-posets
open import order-theory.posets
open import order-theory.postfixpoints-endomaps-posets
open import order-theory.upper-bounds-posets
```

</details>

## Idea

Given an endomap on a [poset](order-theory.posets.md) `f : P → P`, a
{{#concept "greatest postfixpoint" Disambiguation="of an endomap on a poset" Agda=is-greatest-postfixpoint-endomap-Poset}}
is a [postfixpoint](order-theory.postfixpoints-endomaps-posets.md) that is above
all postfixpoints.

If `f` is [increasing](order-theory.order-preserving-maps-posets.md) and `x₀` is
a
[least upper bound of postfixpoints](order-theory.least-upper-bounds-postfixpoints-endomaps-posets.md),
then `x₀` is a greatest postfixpoint of `f`. Therefore `x₀` is a
[fixed point](foundation.fixed-points-endofunctions.md).

## Definitions

```agda
is-greatest-postfixpoint-endomap-Poset :
  {l1 l2 : Level} (P : Poset l1 l2) →
  (type-Poset P → type-Poset P) →
  type-Poset P → UU (l1 ⊔ l2)
is-greatest-postfixpoint-endomap-Poset P f x0 =
  is-postfixpoint-endomap-Poset P f x0 ×
  ( (x : type-Poset P) →
    is-postfixpoint-endomap-Poset P f x →
    leq-Poset P x x0)

module _
  {l1 l2 : Level} (P : Poset l1 l2)
  (f : type-Poset P → type-Poset P) (x0 : type-Poset P)
  (H : is-greatest-postfixpoint-endomap-Poset P f x0)
  where

  is-postfixpoint-is-greatest-postfixpoint-endomap-Poset :
    is-postfixpoint-endomap-Poset P f x0
  is-postfixpoint-is-greatest-postfixpoint-endomap-Poset = pr1 H

  leq-is-postfixpoint-is-greatest-postfixpoint-endomap-Poset :
    (x : type-Poset P) →
    is-postfixpoint-endomap-Poset P f x →
    leq-Poset P x x0
  leq-is-postfixpoint-is-greatest-postfixpoint-endomap-Poset = pr2 H
```

## Properties

### Greatest postfixpoints of increasing endomaps are fixpoints

```agda
module _
  {l1 l2 : Level}
  (P : Poset l1 l2)
  (f : type-Poset P → type-Poset P)
  (is-increasing-f : preserves-order-Poset P P f)
  (x0 : type-Poset P)
  (H : is-least-upper-bound-postfixpoints-endomap-Poset P f x0)
  where

  is-upper-bound-postfixpoints-is-least-upper-bound-postfixpoints-endomap-Poset :
    is-upper-bound-family-of-elements-Poset P
      ( family-of-elements-postfixpoints-endomap-Poset P f)
      ( x0)
  is-upper-bound-postfixpoints-is-least-upper-bound-postfixpoints-endomap-Poset =
    backward-implication
      ( H x0)
      ( refl-leq-Poset P x0)

  leq-postfixpoint-is-least-upper-bound-postfixpoints-endomap-Poset :
    (x : type-Poset P) →
    is-postfixpoint-endomap-Poset P f x →
    leq-Poset P x x0
  leq-postfixpoint-is-least-upper-bound-postfixpoints-endomap-Poset x x≤fx =
    is-upper-bound-postfixpoints-is-least-upper-bound-postfixpoints-endomap-Poset
      (x , x≤fx)

  abstract
    is-upper-bound-postfixpoints-image-is-least-upper-bound-postfixpoints-endomap-Poset :
      is-upper-bound-family-of-elements-Poset
        P
        (family-of-elements-postfixpoints-endomap-Poset P f)
        (f x0)
    is-upper-bound-postfixpoints-image-is-least-upper-bound-postfixpoints-endomap-Poset
      (x , x≤fx) =
      transitive-leq-Poset P x (f x) (f x0)
        ( is-increasing-f x x0
          (leq-postfixpoint-is-least-upper-bound-postfixpoints-endomap-Poset x
            ( x≤fx)))
        ( x≤fx)

    is-postfixpoint-is-least-upper-bound-postfixpoints-endomap-Poset :
      is-postfixpoint-endomap-Poset P f x0
    is-postfixpoint-is-least-upper-bound-postfixpoints-endomap-Poset =
      forward-implication
        ( H (f x0))
        ( is-upper-bound-postfixpoints-image-is-least-upper-bound-postfixpoints-endomap-Poset)

    is-greatest-postfixpoint-is-least-upper-bound-postfixpoints-endomap-Poset :
      is-greatest-postfixpoint-endomap-Poset P f x0
    is-greatest-postfixpoint-is-least-upper-bound-postfixpoints-endomap-Poset =
      ( is-postfixpoint-is-least-upper-bound-postfixpoints-endomap-Poset ,
        leq-postfixpoint-is-least-upper-bound-postfixpoints-endomap-Poset)
```

```agda
abstract
  is-fixed-point-is-greatest-postfixpoint-is-increasing-endomap-Poset :
    {l1 l2 : Level} (P : Poset l1 l2) (f : type-Poset P → type-Poset P) →
    preserves-order-Poset P P f →
    (x0 : type-Poset P) →
    is-greatest-postfixpoint-endomap-Poset P f x0 →
    f x0 ＝ x0
  is-fixed-point-is-greatest-postfixpoint-is-increasing-endomap-Poset
    P f is-increasing-f x0 H =
    antisymmetric-leq-Poset P (f x0) x0
      ( leq-is-postfixpoint-is-greatest-postfixpoint-endomap-Poset P f x0 H
        ( f x0)
        ( is-increasing-f x0 (f x0)
          ( is-postfixpoint-is-greatest-postfixpoint-endomap-Poset P f x0 H)))
      ( is-postfixpoint-is-greatest-postfixpoint-endomap-Poset P f x0 H)
```
