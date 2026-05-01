# Linear maps between real vector spaces

```agda
module linear-algebra.linear-maps-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.linear-maps-vector-spaces
open import linear-algebra.real-vector-spaces

open import real-numbers.field-of-real-numbers
```

</details>

## Idea

A
{{#concept "linear map" Disambiguation="between two real vector spaces" Agda=linear-map-ℝ-Vector-Space}}
between [real vector spaces](linear-algebra.real-vector-spaces.md) `V` and `W`
is a map `f : V → W` such that `f (v₁ + v₂) = f v₁ + f v₂` and
`f (c * v) ＝ c * f v`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (V : ℝ-Vector-Space l1 l2)
  (W : ℝ-Vector-Space l1 l3)
  where

  is-additive-map-prop-ℝ-Vector-Space :
    subtype (l2 ⊔ l3) (type-ℝ-Vector-Space V → type-ℝ-Vector-Space W)
  is-additive-map-prop-ℝ-Vector-Space =
    is-additive-map-prop-Vector-Space (heyting-field-ℝ l1) V W

  is-additive-map-ℝ-Vector-Space :
    (type-ℝ-Vector-Space V → type-ℝ-Vector-Space W) → UU (l2 ⊔ l3)
  is-additive-map-ℝ-Vector-Space =
    is-in-subtype is-additive-map-prop-ℝ-Vector-Space

  is-homogeneous-map-prop-ℝ-Vector-Space :
    subtype (lsuc l1 ⊔ l2 ⊔ l3) (type-ℝ-Vector-Space V → type-ℝ-Vector-Space W)
  is-homogeneous-map-prop-ℝ-Vector-Space =
    is-homogeneous-map-prop-Vector-Space (heyting-field-ℝ l1) V W

  is-homogeneous-map-ℝ-Vector-Space :
    (type-ℝ-Vector-Space V → type-ℝ-Vector-Space W) → UU (lsuc l1 ⊔ l2 ⊔ l3)
  is-homogeneous-map-ℝ-Vector-Space =
    is-in-subtype is-homogeneous-map-prop-ℝ-Vector-Space

  is-linear-map-prop-ℝ-Vector-Space :
    subtype (lsuc l1 ⊔ l2 ⊔ l3) (type-ℝ-Vector-Space V → type-ℝ-Vector-Space W)
  is-linear-map-prop-ℝ-Vector-Space =
    is-linear-map-prop-Vector-Space (heyting-field-ℝ l1) V W

  is-linear-map-ℝ-Vector-Space :
    (type-ℝ-Vector-Space V → type-ℝ-Vector-Space W) → UU (lsuc l1 ⊔ l2 ⊔ l3)
  is-linear-map-ℝ-Vector-Space = is-in-subtype is-linear-map-prop-ℝ-Vector-Space

  linear-map-ℝ-Vector-Space : UU (lsuc l1 ⊔ l2 ⊔ l3)
  linear-map-ℝ-Vector-Space = type-subtype is-linear-map-prop-ℝ-Vector-Space
```
