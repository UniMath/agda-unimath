# Cartesian products of metric spaces

```agda
module metric-spaces.cartesian-products-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.evaluation-functions
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import metric-spaces.extensionality-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.monotonic-rational-neighborhood-relations
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.reflexive-rational-neighborhood-relations
open import metric-spaces.saturated-rational-neighborhood-relations
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.symmetric-rational-neighborhood-relations
open import metric-spaces.triangular-rational-neighborhood-relations
open import metric-spaces.isometries-metric-spaces
open import foundation.diagonal-maps-cartesian-products-of-types
```

</details>

## Idea

For any two [metric spaces](metric-spaces.metric-spaces.md) `X`, `Y`, there is a
{{#concept "cartesian product metric space" Agda=product-Metric-Space}} `X × Y`.
Pairs `(x₁ , y₁)` and `(x₂ , y₂)` are in a
[`d`-neighborhood](metric-spaces.rational-neighborhood-relations.md) in the
product structure if `x₁` and `x₂` are in a `d`-neighborhood and `y₁` and `y₂`
are in a `d`-neighborhood.

This metric is not canonical, but is consistent with the
[dependent product of metric spaces](metric-spaces.dependent-products-metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  where

  type-product-Metric-Space : UU (l1 ⊔ l3)
  type-product-Metric-Space = type-Metric-Space X × type-Metric-Space Y

  neighborhood-prop-product-Metric-Space :
    Rational-Neighborhood-Relation (l2 ⊔ l4) type-product-Metric-Space
  neighborhood-prop-product-Metric-Space ε (x₁ , y₁) (x₂ , y₂) =
    neighborhood-prop-Metric-Space X ε x₁ x₂ ∧
    neighborhood-prop-Metric-Space Y ε y₁ y₂

  refl-neighborhood-product-Metric-Space :
    is-reflexive-Rational-Neighborhood-Relation
      neighborhood-prop-product-Metric-Space
  refl-neighborhood-product-Metric-Space ε (x , y) =
    refl-neighborhood-Metric-Space X ε x ,
    refl-neighborhood-Metric-Space Y ε y

  symmetric-neighborhood-product-Metric-Space :
    is-symmetric-Rational-Neighborhood-Relation
      neighborhood-prop-product-Metric-Space
  symmetric-neighborhood-product-Metric-Space
    ε (x₁ , y₁) (x₂ , y₂) =
      map-product
        ( symmetric-neighborhood-Metric-Space X ε x₁ x₂)
        ( symmetric-neighborhood-Metric-Space Y ε y₁ y₂)

  triangular-neighborhood-product-Metric-Space :
    is-triangular-Rational-Neighborhood-Relation
      neighborhood-prop-product-Metric-Space
  triangular-neighborhood-product-Metric-Space
    (x₁ , y₁) (x₂ , y₂) (x₃ , y₃) d12 d23 (Ndx23 , Ndy23) (Ndx12 , Ndy12) =
      triangular-neighborhood-Metric-Space X x₁ x₂ x₃ d12 d23 Ndx23 Ndx12 ,
      triangular-neighborhood-Metric-Space Y y₁ y₂ y₃ d12 d23 Ndy23 Ndy12

  saturated-neighborhood-product-Metric-Space :
    is-saturated-Rational-Neighborhood-Relation
      neighborhood-prop-product-Metric-Space
  saturated-neighborhood-product-Metric-Space ε (x₁ , y₁) (x₂ , y₂) H =
    saturated-neighborhood-Metric-Space X ε x₁ x₂ (pr1 ∘ H) ,
    saturated-neighborhood-Metric-Space Y ε y₁ y₂ (pr2 ∘ H)

  pseudometric-space-product-Metric-Space :
    Pseudometric-Space (l1 ⊔ l3) (l2 ⊔ l4)
  pseudometric-space-product-Metric-Space =
    type-product-Metric-Space ,
    neighborhood-prop-product-Metric-Space ,
    refl-neighborhood-product-Metric-Space ,
    symmetric-neighborhood-product-Metric-Space ,
    triangular-neighborhood-product-Metric-Space ,
    saturated-neighborhood-product-Metric-Space

  is-extensional-pseudometric-space-product-Metric-Space :
    is-extensional-Pseudometric-Space
      pseudometric-space-product-Metric-Space
  is-extensional-pseudometric-space-product-Metric-Space =
    is-extensional-is-tight-Pseudometric-Space
      ( pseudometric-space-product-Metric-Space)
      ( λ (x₁ , y₁) (x₂ , y₂) H →
        eq-pair
          ( eq-sim-Metric-Space X x₁ x₂ (pr1 ∘ H))
          ( eq-sim-Metric-Space Y y₁ y₂ (pr2 ∘ H)))

  product-Metric-Space : Metric-Space (l1 ⊔ l3) (l2 ⊔ l4)
  product-Metric-Space =
    make-Metric-Space
      type-product-Metric-Space
      neighborhood-prop-product-Metric-Space
      refl-neighborhood-product-Metric-Space
      symmetric-neighborhood-product-Metric-Space
      triangular-neighborhood-product-Metric-Space
      saturated-neighborhood-product-Metric-Space
      is-extensional-pseudometric-space-product-Metric-Space
```

## Properties

### The projection maps are short

```agda
  is-short-map-pr1-product-Metric-Space :
    is-short-map-Metric-Space
      ( product-Metric-Space)
      ( X)
      ( pr1)
  is-short-map-pr1-product-Metric-Space _ _ _ = pr1

  is-short-map-pr2-product-Metric-Space :
    is-short-map-Metric-Space
      ( product-Metric-Space)
      ( Y)
      ( pr2)
  is-short-map-pr2-product-Metric-Space _ _ _ = pr2
```

### The diagonal isometry from `X` to `X × X`

```agda
module _
  {l1 l2 : Level}
  (X : Metric-Space l1 l2)
  where

  diagonal-product-isometry-Metric-Space :
    isometry-Metric-Space X (product-Metric-Space X X)
  diagonal-product-isometry-Metric-Space =
    ( diagonal-product (type-Metric-Space X) ,
      ( λ _ _ _ → ((λ N → (N , N)) , pr1)))
```
