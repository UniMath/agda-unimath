# The addition isometry on real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.isometry-addition-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-space-of-isometries-metric-spaces
open import metric-spaces.modulated-uniformly-continuous-maps-metric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.uniformly-continuous-endomaps-real-numbers
```

</details>

## Idea

For any `a : ℝ`, [addition](real-numbers.addition-real-numbers.md) by `a` is an
[isometry](metric-spaces.isometries-metric-spaces.md) `ℝ → ℝ` for the
[standard real metric structure](real-numbers.metric-space-of-real-numbers.md).
Moreover, the map `x ↦ add-ℝ x` is an isometry from `ℝ` into the
[metric space of isometries](metric-spaces.metric-space-of-isometries-metric-spaces.md)
of `ℝ`.

## Definitions

### Addition with a real number is an isometry `ℝ → ℝ`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1)
  where

  abstract
    is-isometry-left-add-ℝ :
      is-isometry-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( add-ℝ x)
    is-isometry-left-add-ℝ d y z =
      ( λ Nyz →
        neighborhood-real-bound-each-leq-ℝ
          ( d)
          ( add-ℝ x y)
          ( add-ℝ x z)
          ( preserves-lower-neighborhood-leq-left-add-ℝ d x y z
            ( left-leq-real-bound-neighborhood-ℝ d y z Nyz))
          ( preserves-lower-neighborhood-leq-left-add-ℝ d x z y
            ( right-leq-real-bound-neighborhood-ℝ d y z Nyz))) ,
      ( λ Nxyz →
        neighborhood-real-bound-each-leq-ℝ d y z
          ( reflects-lower-neighborhood-leq-left-add-ℝ d x y z
            ( left-leq-real-bound-neighborhood-ℝ d (x +ℝ y) (x +ℝ z) Nxyz))
          ( reflects-lower-neighborhood-leq-left-add-ℝ d x z y
            ( right-leq-real-bound-neighborhood-ℝ d (x +ℝ y) (x +ℝ z) Nxyz)))

    is-isometry-right-add-ℝ :
      is-isometry-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2))
        ( λ y → add-ℝ y x)
    is-isometry-right-add-ℝ =
      tr
        ( is-isometry-Metric-Space
          ( metric-space-ℝ l2)
          ( metric-space-ℝ (l1 ⊔ l2)))
        ( eq-htpy (commutative-add-ℝ x))
        ( is-isometry-left-add-ℝ)

  isometry-left-add-ℝ :
    isometry-Metric-Space
      ( metric-space-ℝ l2)
      ( metric-space-ℝ (l1 ⊔ l2))
  isometry-left-add-ℝ = (add-ℝ x , is-isometry-left-add-ℝ)

  isometry-right-add-ℝ :
    isometry-Metric-Space
      ( metric-space-ℝ l2)
      ( metric-space-ℝ (l1 ⊔ l2))
  isometry-right-add-ℝ = ( (λ y → add-ℝ y x) , is-isometry-right-add-ℝ)

  short-map-left-add-ℝ :
    short-map-Metric-Space
      ( metric-space-ℝ l2)
      ( metric-space-ℝ (l1 ⊔ l2))
  short-map-left-add-ℝ =
    short-map-isometry-Metric-Space
      ( metric-space-ℝ l2)
      ( metric-space-ℝ (l1 ⊔ l2))
      ( isometry-left-add-ℝ)

  uniformly-continuous-right-add-ℝ : uniformly-continuous-endomap-ℝ l2 (l1 ⊔ l2)
  uniformly-continuous-right-add-ℝ =
    uniformly-continuous-map-isometry-Metric-Space
      ( metric-space-ℝ l2)
      ( metric-space-ℝ (l1 ⊔ l2))
      ( isometry-right-add-ℝ)
```

### Addition is an isometry from `ℝ` to the metric space of isometries `ℝ → ℝ`

```agda
module _
  {l1 l2 : Level}
  where

  is-isometry-isometry-left-add-ℝ :
    is-isometry-Metric-Space
      ( metric-space-ℝ l1)
      ( metric-space-of-isometries-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2)))
      ( isometry-left-add-ℝ)
  is-isometry-isometry-left-add-ℝ d x y =
    ( λ Nxy z →
      neighborhood-real-bound-each-leq-ℝ
        ( d)
        ( add-ℝ x z)
        ( add-ℝ y z)
        ( preserves-lower-neighborhood-leq-right-add-ℝ d z x y
          ( left-leq-real-bound-neighborhood-ℝ d x y Nxy))
        ( preserves-lower-neighborhood-leq-right-add-ℝ d z y x
          ( right-leq-real-bound-neighborhood-ℝ d x y Nxy))) ,
    ( λ Nxyz →
      neighborhood-real-bound-each-leq-ℝ d x y
        ( reflects-lower-neighborhood-leq-right-add-ℝ
          ( d)
          ( raise-ℝ l2 zero-ℝ)
          ( x)
          ( y)
          ( left-leq-real-bound-neighborhood-ℝ
            ( d)
            ( x +ℝ raise-zero-ℝ l2)
            ( y +ℝ raise-zero-ℝ l2)
            ( Nxyz (raise-zero-ℝ l2))))
        ( reflects-lower-neighborhood-leq-right-add-ℝ
          ( d)
          ( raise-zero-ℝ l2)
          ( y)
          ( x)
          ( right-leq-real-bound-neighborhood-ℝ
            ( d)
            ( x +ℝ raise-zero-ℝ l2)
            ( y +ℝ raise-zero-ℝ l2)
            ( Nxyz (raise-zero-ℝ l2)))))

  isometry-add-ℝ :
    isometry-Metric-Space
      ( metric-space-ℝ l1)
      ( metric-space-of-isometries-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2)))
  isometry-add-ℝ = (isometry-left-add-ℝ , is-isometry-isometry-left-add-ℝ)
```

### Addition is a modulated uniformly continuous function on the product of the metric space of reals with itself

```agda
modulated-ucont-map-add-pair-ℝ :
  (l1 l2 : Level) →
  modulated-ucont-map-Metric-Space
    ( product-Metric-Space (metric-space-ℝ l1) (metric-space-ℝ l2))
    ( metric-space-ℝ (l1 ⊔ l2))
modulated-ucont-map-add-pair-ℝ l1 l2 =
  modulated-ucont-uncurry-map-is-binary-isometry-Metric-Space
    ( metric-space-ℝ l1)
    ( metric-space-ℝ l2)
    ( metric-space-ℝ (l1 ⊔ l2))
    ( add-ℝ)
    ( is-isometry-left-add-ℝ)
    ( is-isometry-right-add-ℝ)
```

### Addition is a modulated uniformly continuous function on the product of the metric space of reals with itself

```agda
uniformly-continuous-map-add-pair-ℝ :
  (l1 l2 : Level) →
  uniformly-continuous-map-Metric-Space
    ( product-Metric-Space (metric-space-ℝ l1) (metric-space-ℝ l2))
    ( metric-space-ℝ (l1 ⊔ l2))
uniformly-continuous-map-add-pair-ℝ l1 l2 =
  uniformly-continuous-map-modulated-ucont-map-Metric-Space
    ( product-Metric-Space (metric-space-ℝ l1) (metric-space-ℝ l2))
    ( metric-space-ℝ (l1 ⊔ l2))
    ( modulated-ucont-map-add-pair-ℝ l1 l2)
```
