# Greatest postfixpoints of endomaps on the MacNeille reals

```agda
module real-numbers.greatest-postfixpoints-endomaps-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.universe-levels

open import order-theory.greatest-postfixpoints-endomaps-posets

open import real-numbers.increasing-endomaps-macneille-real-numbers
open import real-numbers.inequality-macneille-real-numbers
open import real-numbers.least-upper-bounds-postfixpoints-endomaps-macneille-real-numbers
open import real-numbers.macneille-real-numbers
open import real-numbers.postfixpoints-endomaps-macneille-real-numbers
open import real-numbers.upper-bounds-families-macneille-real-numbers
```

</details>

## Idea

Given an endomap `f` on the
[MacNeille reals](real-numbers.macneille-real-numbers.md), a
{{#concept "greatest postfixpoint" Disambiguation="of an endomap on the MacNeille reals" Agda=is-greatest-postfixpoint-endomap-macneille-ℝ}}
is a
[postfixpoint](real-numbers.postfixpoints-endomaps-macneille-real-numbers.md)
that is above all postfixpoints.

If `f` is
[increasing](real-numbers.increasing-endomaps-macneille-real-numbers.md) and
`x₀` is a
[least upper bound of postfixpoints](real-numbers.least-upper-bounds-postfixpoints-endomaps-macneille-real-numbers.md),
then `x₀` is a greatest postfixpoint of `f`. Therefore `x₀` is a
[fixed point](foundation.fixed-points-endofunctions.md).

## Definitions

```agda
is-greatest-postfixpoint-endomap-macneille-ℝ :
  {l : Level} (g : macneille-ℝ l → macneille-ℝ l) →
  macneille-ℝ l → UU (lsuc l)
is-greatest-postfixpoint-endomap-macneille-ℝ {l} =
  is-greatest-postfixpoint-endomap-Poset
    ( poset-macneille-ℝ l)

is-postfixpoint-is-greatest-postfixpoint-endomap-macneille-ℝ :
  {l : Level} (g : macneille-ℝ l → macneille-ℝ l) (x0 : macneille-ℝ l) →
  is-greatest-postfixpoint-endomap-macneille-ℝ g x0 →
  is-postfixpoint-endomap-macneille-ℝ g x0
is-postfixpoint-is-greatest-postfixpoint-endomap-macneille-ℝ {l} =
  is-postfixpoint-is-greatest-postfixpoint-endomap-Poset
    ( poset-macneille-ℝ l)

leq-is-postfixpoint-is-greatest-postfixpoint-endomap-macneille-ℝ :
  {l : Level} (g : macneille-ℝ l → macneille-ℝ l) (x0 : macneille-ℝ l) →
  is-greatest-postfixpoint-endomap-macneille-ℝ g x0 →
  (x : macneille-ℝ l) →
  is-postfixpoint-endomap-macneille-ℝ g x →
  leq-macneille-ℝ x x0
leq-is-postfixpoint-is-greatest-postfixpoint-endomap-macneille-ℝ {l} =
  leq-is-postfixpoint-is-greatest-postfixpoint-endomap-Poset
    ( poset-macneille-ℝ l)
```

## Properties

### Greatest postfixpoints of increasing endomaps are fixpoints

```agda
module _
  {l : Level}
  (g : macneille-ℝ l → macneille-ℝ l)
  (is-increasing-g : is-increasing-endomap-macneille-ℝ g)
  (x0 : macneille-ℝ l)
  (H : is-least-upper-bound-postfixpoints-endomap-macneille-ℝ g x0)
  where

  is-upper-bound-postfixpoints-is-least-upper-bound-postfixpoints-endomap-macneille-ℝ :
    is-upper-bound-family-of-elements-macneille-ℝ
      ( family-of-elements-postfixpoints-endomap-macneille-ℝ g)
      ( x0)
  is-upper-bound-postfixpoints-is-least-upper-bound-postfixpoints-endomap-macneille-ℝ =
    is-upper-bound-postfixpoints-is-least-upper-bound-postfixpoints-endomap-Poset
      ( poset-macneille-ℝ l)
      ( g)
      ( is-increasing-g)
      ( x0)
      ( H)

  leq-postfixpoint-is-least-upper-bound-postfixpoints-endomap-macneille-ℝ :
    (x : macneille-ℝ l) →
    is-postfixpoint-endomap-macneille-ℝ g x →
    leq-macneille-ℝ x x0
  leq-postfixpoint-is-least-upper-bound-postfixpoints-endomap-macneille-ℝ =
    leq-postfixpoint-is-least-upper-bound-postfixpoints-endomap-Poset
      ( poset-macneille-ℝ l)
      ( g)
      ( is-increasing-g)
      ( x0)
      ( H)

  abstract
    is-upper-bound-postfixpoints-image-is-least-upper-bound-postfixpoints-endomap-macneille-ℝ :
      is-upper-bound-family-of-elements-macneille-ℝ
        ( family-of-elements-postfixpoints-endomap-macneille-ℝ g)
        ( g x0)
    is-upper-bound-postfixpoints-image-is-least-upper-bound-postfixpoints-endomap-macneille-ℝ =
      is-upper-bound-postfixpoints-image-is-least-upper-bound-postfixpoints-endomap-Poset
        ( poset-macneille-ℝ l)
        ( g)
        ( is-increasing-g)
        ( x0)
        ( H)

    is-postfixpoint-is-least-upper-bound-postfixpoints-endomap-macneille-ℝ :
      is-postfixpoint-endomap-macneille-ℝ g x0
    is-postfixpoint-is-least-upper-bound-postfixpoints-endomap-macneille-ℝ =
      is-postfixpoint-is-least-upper-bound-postfixpoints-endomap-Poset
        ( poset-macneille-ℝ l)
        ( g)
        ( is-increasing-g)
        ( x0)
        ( H)

    is-greatest-postfixpoint-is-least-upper-bound-postfixpoints-endomap-macneille-ℝ :
      is-greatest-postfixpoint-endomap-macneille-ℝ g x0
    is-greatest-postfixpoint-is-least-upper-bound-postfixpoints-endomap-macneille-ℝ =
      is-greatest-postfixpoint-is-least-upper-bound-postfixpoints-endomap-Poset
        ( poset-macneille-ℝ l)
        ( g)
        ( is-increasing-g)
        ( x0)
        ( H)
```

```agda
abstract
  is-fixed-point-is-greatest-postfixpoint-is-increasing-endomap-macneille-ℝ :
    {l : Level} (g : macneille-ℝ l → macneille-ℝ l) →
    is-increasing-endomap-macneille-ℝ g →
    (x0 : macneille-ℝ l) →
    is-greatest-postfixpoint-endomap-macneille-ℝ g x0 →
    g x0 ＝ x0
  is-fixed-point-is-greatest-postfixpoint-is-increasing-endomap-macneille-ℝ
    {l} =
    is-fixed-point-is-greatest-postfixpoint-is-increasing-endomap-Poset
      ( poset-macneille-ℝ l)
```
