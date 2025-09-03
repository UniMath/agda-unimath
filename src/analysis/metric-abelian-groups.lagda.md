# Metric abelian groups

```agda
module analysis.metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups

open import metric-spaces.extensionality-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
```

</details>

## Idea

A {{#concept "metric abelian group" Agda=Metric-Ab}} is an
[abelian group](group-theory.abelian-groups.md) endowed with the structure of a
[metric space](metric-spaces.metric-spaces.md) such that the addition operation
and negation operation are
[isometries](metric-spaces.isometries-metric-spaces.md).

## Definition

```agda
Metric-Ab : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Metric-Ab l1 l2 =
  Σ ( Ab l1)
    ( λ G →
      Σ ( Pseudometric-Structure l2 (type-Ab G))
        ( λ M →
          let MS = (type-Ab G , M)
          in
            is-extensional-Pseudometric-Space MS ×
            is-isometry-Pseudometric-Space MS MS (neg-Ab G) ×
            ( (x : type-Ab G) →
              is-isometry-Pseudometric-Space MS MS (add-Ab G x))))

module _
  {l1 l2 : Level} (MG : Metric-Ab l1 l2)
  where

  ab-Metric-Ab : Ab l1
  ab-Metric-Ab = pr1 MG

  type-Metric-Ab : UU l1
  type-Metric-Ab = type-Ab ab-Metric-Ab
```

### Abelian group properties of metric abelian groups

```agda
module _
  {l1 l2 : Level} (MG : Metric-Ab l1 l2)
  where

  zero-Metric-Ab : type-Metric-Ab MG
  zero-Metric-Ab = zero-Ab (ab-Metric-Ab MG)

  add-Metric-Ab : type-Metric-Ab MG → type-Metric-Ab MG → type-Metric-Ab MG
  add-Metric-Ab = add-Ab (ab-Metric-Ab MG)

  add-Metric-Ab' : type-Metric-Ab MG → type-Metric-Ab MG → type-Metric-Ab MG
  add-Metric-Ab' = add-Ab' (ab-Metric-Ab MG)

  ap-add-Metric-Ab :
    {x x' y y' : type-Metric-Ab MG} → x ＝ x' → y ＝ y' →
    add-Metric-Ab x y ＝ add-Metric-Ab x' y'
  ap-add-Metric-Ab = ap-add-Ab (ab-Metric-Ab MG)

  neg-Metric-Ab : type-Metric-Ab MG → type-Metric-Ab MG
  neg-Metric-Ab = neg-Ab (ab-Metric-Ab MG)

  diff-Metric-Ab : type-Metric-Ab MG → type-Metric-Ab MG → type-Metric-Ab MG
  diff-Metric-Ab x y = add-Metric-Ab x (neg-Metric-Ab y)

  ap-diff-Metric-Ab :
    {x x' y y' : type-Metric-Ab MG} → x ＝ x' → y ＝ y' →
    diff-Metric-Ab x y ＝ diff-Metric-Ab x' y'
  ap-diff-Metric-Ab = ap-right-subtraction-Ab (ab-Metric-Ab MG)

  commutative-add-Metric-Ab :
    (x y : type-Metric-Ab MG) → add-Metric-Ab x y ＝ add-Metric-Ab y x
  commutative-add-Metric-Ab = commutative-add-Ab (ab-Metric-Ab MG)
```

### Metric properties of metric abelian groups

```agda
module _
  {l1 l2 : Level} (MG : Metric-Ab l1 l2)
  where

  pseudometric-structure-Metric-Ab :
    Pseudometric-Structure l2 (type-Metric-Ab MG)
  pseudometric-structure-Metric-Ab = pr1 (pr2 MG)

  pseudometric-space-Metric-Ab : Pseudometric-Space l1 l2
  pseudometric-space-Metric-Ab =
    ( type-Metric-Ab MG , pseudometric-structure-Metric-Ab)

  metric-space-Metric-Ab : Metric-Space l1 l2
  metric-space-Metric-Ab =
    ( pseudometric-space-Metric-Ab ,
      pr1 (pr2 (pr2 MG)))

  neighborhood-prop-Metric-Ab :
    Rational-Neighborhood-Relation l2 (type-Metric-Ab MG)
  neighborhood-prop-Metric-Ab =
    neighborhood-prop-Metric-Space metric-space-Metric-Ab

  neighborhood-Metric-Ab : ℚ⁺ → Relation l2 (type-Metric-Ab MG)
  neighborhood-Metric-Ab = neighborhood-Metric-Space metric-space-Metric-Ab

  is-isometry-add-Metric-Ab :
    (x : type-Metric-Ab MG) →
    is-isometry-Metric-Space
      ( metric-space-Metric-Ab)
      ( metric-space-Metric-Ab)
      ( add-Metric-Ab MG x)
  is-isometry-add-Metric-Ab = pr2 (pr2 (pr2 (pr2 MG)))

  isometry-add-Metric-Ab :
    (x : type-Metric-Ab MG) →
    isometry-Metric-Space
      ( metric-space-Metric-Ab)
      ( metric-space-Metric-Ab)
  isometry-add-Metric-Ab x = (add-Metric-Ab MG x , is-isometry-add-Metric-Ab x)

  is-isometry-neg-Metric-Ab :
    is-isometry-Metric-Space
      ( metric-space-Metric-Ab)
      ( metric-space-Metric-Ab)
      ( neg-Metric-Ab MG)
  is-isometry-neg-Metric-Ab = pr1 (pr2 (pr2 (pr2 MG)))

  isometry-neg-Metric-Ab :
    isometry-Metric-Space
      ( metric-space-Metric-Ab)
      ( metric-space-Metric-Ab)
  isometry-neg-Metric-Ab = (neg-Metric-Ab MG , is-isometry-neg-Metric-Ab)
```
