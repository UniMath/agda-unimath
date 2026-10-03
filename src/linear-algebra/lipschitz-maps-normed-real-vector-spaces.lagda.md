# Lipschitz maps between normed real vector spaces

```agda
module linear-algebra.lipschitz-maps-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.existential-quantification
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.normed-real-vector-spaces

open import logic.functoriality-existential-quantification

open import metric-spaces.lipschitz-maps-metric-spaces

open import order-theory.large-posets

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

To show that a map `f : V → W` between
[normed real vector spaces](linear-algebra.normed-real-vector-spaces.md) is
[Lipschitz continuous](metric-spaces.lipschitz-maps-metric-spaces.md), it
suffices to demonstrate the
[existence](foundation.existential-quantification.md) of a
[nonnegative real number](real-numbers.nonnegative-real-numbers.md) `c` such
that for any `x y : V`, `d (f x) (f y) ≤ c * d x y`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (W : Normed-ℝ-Vector-Space l3 l4)
  where

  is-lipschitz-prop-map-Normed-ℝ-Vector-Space :
    subtype
      ( l1 ⊔ l2 ⊔ l3)
      ( type-Normed-ℝ-Vector-Space V → type-Normed-ℝ-Vector-Space W)
  is-lipschitz-prop-map-Normed-ℝ-Vector-Space =
    is-lipschitz-prop-map-Metric-Space
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( metric-space-Normed-ℝ-Vector-Space W)

  is-lipschitz-map-Normed-ℝ-Vector-Space :
    (type-Normed-ℝ-Vector-Space V → type-Normed-ℝ-Vector-Space W) →
    UU (l1 ⊔ l2 ⊔ l3)
  is-lipschitz-map-Normed-ℝ-Vector-Space =
    is-in-subtype is-lipschitz-prop-map-Normed-ℝ-Vector-Space

  lipschitz-map-Normed-ℝ-Vector-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  lipschitz-map-Normed-ℝ-Vector-Space =
    type-subtype is-lipschitz-prop-map-Normed-ℝ-Vector-Space
```

## Properties

### Proving a map is Lipschitz

```agda
module _
  {l1 l2 l3 l4 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (W : Normed-ℝ-Vector-Space l3 l4)
  (f : type-Normed-ℝ-Vector-Space V → type-Normed-ℝ-Vector-Space W)
  where abstract

  open inequality-reasoning-Large-Poset ℝ-Large-Poset

  is-lipschitz-real-constant-map-Normed-ℝ-Vector-Space :
    {l5 : Level} (c : ℝ⁰⁺ l5) →
    ((x y : type-Normed-ℝ-Vector-Space V) →
      leq-ℝ
        ( dist-Normed-ℝ-Vector-Space W (f x) (f y))
        ( real-ℝ⁰⁺ c *ℝ dist-Normed-ℝ-Vector-Space V x y)) →
    is-lipschitz-map-Normed-ℝ-Vector-Space V W f
  is-lipschitz-real-constant-map-Normed-ℝ-Vector-Space c⁰⁺@(c , _) K =
    map-tot-exists
      ( λ q c<q d x y dxy≤d →
        chain-of-inequalities
          dist-Normed-ℝ-Vector-Space W (f x) (f y)
          ≤ c *ℝ dist-Normed-ℝ-Vector-Space V x y
            by K x y
          ≤ real-ℚ⁺ q *ℝ real-ℚ⁺ d
            by
              preserves-leq-mul-ℝ⁰⁺
                ( c⁰⁺)
                ( nonnegative-real-ℚ⁺ q)
                ( nonnegative-dist-Normed-ℝ-Vector-Space V x y)
                ( nonnegative-real-ℚ⁺ d)
                ( leq-le-ℝ c<q)
                ( dxy≤d)
          ≤ real-ℚ⁺ (q *ℚ⁺ d)
            by leq-eq-ℝ (mul-real-ℚ _ _))
      ( exists-greater-positive-rational-ℝ c)
```
