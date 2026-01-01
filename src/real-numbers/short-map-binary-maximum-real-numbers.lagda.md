# The binary maximum of real numbers is a short function

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.short-map-binary-maximum-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.metric-space-of-short-maps-metric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces

open import order-theory.least-upper-bounds-large-posets

open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.binary-maximum-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.uniformly-continuous-endofunctions-real-numbers
```

</details>

## Idea

For any `a : ℝ`, the
[binary maximum](real-numbers.binary-maximum-real-numbers.md) with `a` is a
[short function](metric-spaces.short-maps-metric-spaces.md) `ℝ → ℝ` for the
[standard real metric structure](real-numbers.metric-space-of-real-numbers.md).
Moreover, the map `x ↦ max-ℝ x` is a short function from `ℝ` into the
[metric space of short functions](metric-spaces.metric-space-of-short-maps-metric-spaces.md)
of `ℝ`.

## Proof

### The binary maximum preserves lower neighborhoods

```agda
module _
  {l1 l2 l3 : Level} (d : ℚ⁺)
  (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    preserves-lower-neighborhood-leq-left-max-ℝ :
      leq-ℝ y (z +ℝ real-ℚ⁺ d) →
      leq-ℝ
        ( max-ℝ x y)
        ( (max-ℝ x z) +ℝ real-ℚ⁺ d)
    preserves-lower-neighborhood-leq-left-max-ℝ z≤y+d =
      leq-is-least-binary-upper-bound-Large-Poset
        ( ℝ-Large-Poset)
        ( x)
        ( y)
        ( is-least-binary-upper-bound-max-ℝ x y)
        ( (max-ℝ x z) +ℝ real-ℚ⁺ d)
        ( ( transitive-leq-ℝ
            ( x)
            ( max-ℝ x z)
            ( max-ℝ x z +ℝ real-ℚ⁺ d)
            ( leq-le-ℝ
              ( le-left-add-real-ℝ⁺
                ( max-ℝ x z)
                ( positive-real-ℚ⁺ d)))
            ( leq-left-max-ℝ x z)) ,
          ( transitive-leq-ℝ
            ( y)
            ( z +ℝ real-ℚ⁺ d)
            ( max-ℝ x z +ℝ real-ℚ⁺ d)
            ( preserves-leq-right-add-ℝ
              ( real-ℚ⁺ d)
              ( z)
              ( max-ℝ x z)
              ( leq-right-max-ℝ x z))
            ( z≤y+d)))

    preserves-lower-neighborhood-leq-right-max-ℝ :
      leq-ℝ y (z +ℝ real-ℚ⁺ d) →
      leq-ℝ
        ( max-ℝ y x)
        ( (max-ℝ z x) +ℝ real-ℚ⁺ d)
    preserves-lower-neighborhood-leq-right-max-ℝ z≤y+d =
      binary-tr
        ( λ u v → leq-ℝ u (v +ℝ real-ℚ⁺ d))
        ( commutative-max-ℝ x y)
        ( commutative-max-ℝ x z)
        ( preserves-lower-neighborhood-leq-left-max-ℝ z≤y+d)
```

### The maximum with a real number is a short function `ℝ → ℝ`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1)
  where

  abstract
    is-short-map-left-max-ℝ :
      is-short-map-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( max-ℝ x)
    is-short-map-left-max-ℝ d y z Nyz =
      neighborhood-real-bound-each-leq-ℝ
        ( d)
        ( max-ℝ x y)
        ( max-ℝ x z)
        ( preserves-lower-neighborhood-leq-left-max-ℝ d x y z
          ( left-leq-real-bound-neighborhood-ℝ d y z Nyz))
        ( preserves-lower-neighborhood-leq-left-max-ℝ d x z y
          ( right-leq-real-bound-neighborhood-ℝ d y z Nyz))

  short-map-left-max-ℝ :
    short-map-Metric-Space
      ( metric-space-ℝ l2)
      ( metric-space-ℝ (l1 ⊔ l2))
  short-map-left-max-ℝ =
    (max-ℝ x , is-short-map-left-max-ℝ)

  uniformly-continuous-map-left-max-ℝ : uniformly-continuous-endo-ℝ l2 (l1 ⊔ l2)
  uniformly-continuous-map-left-max-ℝ =
    uniformly-continuous-map-short-map-Metric-Space
      ( metric-space-ℝ l2)
      ( metric-space-ℝ (l1 ⊔ l2))
      ( short-map-left-max-ℝ)
```

### The binary maximum is a short function from `ℝ` to the metric space of short functions `ℝ → ℝ`

```agda
module _
  {l1 l2 : Level}
  where

  abstract
    is-short-map-left-max-ℝ :
      is-short-map-Metric-Space
        ( metric-space-ℝ l1)
        ( metric-space-of-short-maps-Metric-Space
          ( metric-space-ℝ l2)
          ( metric-space-ℝ (l1 ⊔ l2)))
        ( short-map-left-max-ℝ)
    is-short-map-left-max-ℝ d x y Nxy z =
      neighborhood-real-bound-each-leq-ℝ
        ( d)
        ( max-ℝ x z)
        ( max-ℝ y z)
        ( preserves-lower-neighborhood-leq-right-max-ℝ d z x y
          ( left-leq-real-bound-neighborhood-ℝ d x y Nxy))
        ( preserves-lower-neighborhood-leq-right-max-ℝ d z y x
          ( right-leq-real-bound-neighborhood-ℝ d x y Nxy))

  short-map-max-ℝ :
    short-map-Metric-Space
      ( metric-space-ℝ l1)
      ( metric-space-of-short-maps-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2)))
  short-map-max-ℝ =
    (short-map-left-max-ℝ , is-short-map-left-max-ℝ)
```
