# Metric abelian groups

```agda
module analysis.metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.extensionality-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.modulated-uniformly-continuous-maps-metric-spaces
open import metric-spaces.monotonic-rational-neighborhood-relations
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.reflexive-rational-neighborhood-relations
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
open import metric-spaces.triangular-rational-neighborhood-relations
open import metric-spaces.uniformly-continuous-maps-metric-spaces
```

</details>

## Idea

A {{#concept "metric abelian group" Agda=Metric-Ab}} is an
[abelian group](group-theory.abelian-groups.md) endowed with the structure of a
[metric space](metric-spaces.metric-spaces.md) such that the addition operation
and negation operation are [short](metric-spaces.short-maps-metric-spaces.md)
(which, together with the group operations, implies they are
[isometries](metric-spaces.isometries-metric-spaces.md)).

## Definition

```agda
is-metric-ab-prop-Ab-Pseudometric-Structure :
  {l1 l2 : Level} (G : Ab l1) (M : Pseudometric-Structure l2 (type-Ab G)) →
  Prop (l1 ⊔ l2)
is-metric-ab-prop-Ab-Pseudometric-Structure G M =
  let
    MS = (type-Ab G , M)
  in
    is-extensional-prop-Pseudometric-Space MS ∧
    is-short-map-prop-Pseudometric-Space MS MS (neg-Ab G) ∧
    Π-Prop
      ( type-Ab G)
      ( λ x → is-short-map-prop-Pseudometric-Space MS MS (add-Ab G x))

is-metric-ab-Ab-Pseudometric-Structure :
  {l1 l2 : Level} (G : Ab l1) (M : Pseudometric-Structure l2 (type-Ab G)) →
  UU (l1 ⊔ l2)
is-metric-ab-Ab-Pseudometric-Structure G M =
  type-Prop (is-metric-ab-prop-Ab-Pseudometric-Structure G M)

Metric-Ab : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Metric-Ab l1 l2 =
  Σ ( Ab l1)
    ( λ G →
      Σ ( Pseudometric-Structure l2 (type-Ab G))
        ( is-metric-ab-Ab-Pseudometric-Structure G))

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
  (let ab-MG = ab-Metric-Ab MG)
  where

  zero-Metric-Ab : type-Metric-Ab MG
  zero-Metric-Ab = zero-Ab ab-MG

  add-Metric-Ab : type-Metric-Ab MG → type-Metric-Ab MG → type-Metric-Ab MG
  add-Metric-Ab = add-Ab ab-MG

  add-Metric-Ab' : type-Metric-Ab MG → type-Metric-Ab MG → type-Metric-Ab MG
  add-Metric-Ab' = add-Ab' ab-MG

  ap-add-Metric-Ab :
    {x x' y y' : type-Metric-Ab MG} → x ＝ x' → y ＝ y' →
    add-Metric-Ab x y ＝ add-Metric-Ab x' y'
  ap-add-Metric-Ab = ap-add-Ab ab-MG

  neg-Metric-Ab : type-Metric-Ab MG → type-Metric-Ab MG
  neg-Metric-Ab = neg-Ab ab-MG

  abstract
    left-unit-law-add-Metric-Ab :
      (x : type-Metric-Ab MG) → add-Metric-Ab zero-Metric-Ab x ＝ x
    left-unit-law-add-Metric-Ab = left-unit-law-add-Ab ab-MG

    associative-add-Metric-Ab :
      (x y z : type-Metric-Ab MG) →
      add-Metric-Ab (add-Metric-Ab x y) z ＝ add-Metric-Ab x (add-Metric-Ab y z)
    associative-add-Metric-Ab = associative-add-Ab ab-MG

    left-inverse-law-add-Metric-Ab :
      (x : type-Metric-Ab MG) →
      add-Metric-Ab (neg-Metric-Ab x) x ＝ zero-Metric-Ab
    left-inverse-law-add-Metric-Ab = left-inverse-law-add-Ab ab-MG

    right-inverse-law-add-Metric-Ab :
      (x : type-Metric-Ab MG) →
      add-Metric-Ab x (neg-Metric-Ab x) ＝ zero-Metric-Ab
    right-inverse-law-add-Metric-Ab = right-inverse-law-add-Ab ab-MG

    neg-zero-Metric-Ab : neg-Metric-Ab zero-Metric-Ab ＝ zero-Metric-Ab
    neg-zero-Metric-Ab = neg-zero-Ab ab-MG

    neg-neg-Metric-Ab :
      (x : type-Metric-Ab MG) → neg-Metric-Ab (neg-Metric-Ab x) ＝ x
    neg-neg-Metric-Ab = neg-neg-Ab ab-MG

  diff-Metric-Ab : type-Metric-Ab MG → type-Metric-Ab MG → type-Metric-Ab MG
  diff-Metric-Ab x y = add-Metric-Ab x (neg-Metric-Ab y)

  ap-diff-Metric-Ab :
    {x x' y y' : type-Metric-Ab MG} → x ＝ x' → y ＝ y' →
    diff-Metric-Ab x y ＝ diff-Metric-Ab x' y'
  ap-diff-Metric-Ab = ap-right-subtraction-Ab ab-MG

  commutative-add-Metric-Ab :
    (x y : type-Metric-Ab MG) → add-Metric-Ab x y ＝ add-Metric-Ab y x
  commutative-add-Metric-Ab = commutative-add-Ab ab-MG

  is-identity-right-conjugation-Metric-Ab :
    (x y : type-Metric-Ab MG) → add-Metric-Ab x (diff-Metric-Ab y x) ＝ y
  is-identity-right-conjugation-Metric-Ab =
    is-identity-right-conjugation-Ab ab-MG
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

  refl-neighborhood-Metric-Ab :
    is-reflexive-Rational-Neighborhood-Relation neighborhood-prop-Metric-Ab
  refl-neighborhood-Metric-Ab =
    refl-neighborhood-Metric-Space metric-space-Metric-Ab

  monotonic-neighborhood-Metric-Ab :
    is-monotonic-Rational-Neighborhood-Relation neighborhood-prop-Metric-Ab
  monotonic-neighborhood-Metric-Ab =
    monotonic-neighborhood-Metric-Space metric-space-Metric-Ab

  triangular-neighborhood-Metric-Ab :
    is-triangular-Rational-Neighborhood-Relation neighborhood-prop-Metric-Ab
  triangular-neighborhood-Metric-Ab =
    triangular-neighborhood-Metric-Space metric-space-Metric-Ab

  is-short-map-add-Metric-Ab :
    (x : type-Metric-Ab MG) →
    is-short-map-Metric-Space
      ( metric-space-Metric-Ab)
      ( metric-space-Metric-Ab)
      ( add-Metric-Ab MG x)
  is-short-map-add-Metric-Ab = pr2 (pr2 (pr2 (pr2 MG)))

  abstract
    reflects-neighborhoods-left-add-Metric-Ab :
      (x : type-Metric-Ab MG)
      (d : ℚ⁺)
      (y z : type-Metric-Ab MG) →
      neighborhood-Metric-Ab
        ( d)
        ( add-Metric-Ab MG x y)
        ( add-Metric-Ab MG x z) →
      neighborhood-Metric-Ab d y z
    reflects-neighborhoods-left-add-Metric-Ab x d y z Nd⟨x+y⟩⟨x+z⟩ =
      binary-tr
        ( neighborhood-Metric-Ab d)
        ( is-retraction-left-subtraction-Ab (ab-Metric-Ab MG) x y)
        ( is-retraction-left-subtraction-Ab (ab-Metric-Ab MG) x z)
        ( is-short-map-add-Metric-Ab (neg-Metric-Ab MG x) d _ _ Nd⟨x+y⟩⟨x+z⟩)

  is-isometry-add-Metric-Ab :
    (x : type-Metric-Ab MG) →
    is-isometry-Metric-Space
      ( metric-space-Metric-Ab)
      ( metric-space-Metric-Ab)
      ( add-Metric-Ab MG x)
  is-isometry-add-Metric-Ab x d y z =
    ( is-short-map-add-Metric-Ab x d y z ,
      reflects-neighborhoods-left-add-Metric-Ab x d y z)

  isometry-add-Metric-Ab :
    (x : type-Metric-Ab MG) →
    isometry-Metric-Space
      ( metric-space-Metric-Ab)
      ( metric-space-Metric-Ab)
  isometry-add-Metric-Ab x = (add-Metric-Ab MG x , is-isometry-add-Metric-Ab x)

  abstract
    is-isometry-add-Metric-Ab' :
      (x : type-Metric-Ab MG) →
      is-isometry-Metric-Space
        ( metric-space-Metric-Ab)
        ( metric-space-Metric-Ab)
        ( add-Metric-Ab' MG x)
    is-isometry-add-Metric-Ab' x =
      tr
        ( is-isometry-Metric-Space
          ( metric-space-Metric-Ab)
          ( metric-space-Metric-Ab))
        ( eq-htpy (commutative-add-Metric-Ab MG x))
        ( is-isometry-add-Metric-Ab x)

  isometry-add-Metric-Ab' :
    (x : type-Metric-Ab MG) →
    isometry-Metric-Space
      ( metric-space-Metric-Ab)
      ( metric-space-Metric-Ab)
  isometry-add-Metric-Ab' x =
    ( add-Metric-Ab' MG x , is-isometry-add-Metric-Ab' x)

  is-short-map-neg-Metric-Ab :
    is-short-map-Metric-Space
      ( metric-space-Metric-Ab)
      ( metric-space-Metric-Ab)
      ( neg-Metric-Ab MG)
  is-short-map-neg-Metric-Ab = pr1 (pr2 (pr2 (pr2 MG)))

  abstract
    reflects-neighborhoods-neg-Metric-Ab :
      (d : ℚ⁺) (x y : type-Metric-Ab MG) →
      neighborhood-Metric-Ab d (neg-Metric-Ab MG x) (neg-Metric-Ab MG y) →
      neighborhood-Metric-Ab d x y
    reflects-neighborhoods-neg-Metric-Ab d x y Nd⟨-x⟩⟨-y⟩ =
      binary-tr
        ( neighborhood-Metric-Ab d)
        ( neg-neg-Metric-Ab MG x)
        ( neg-neg-Metric-Ab MG y)
        ( is-short-map-neg-Metric-Ab d _ _ Nd⟨-x⟩⟨-y⟩)

  is-isometry-neg-Metric-Ab :
    is-isometry-Metric-Space
      ( metric-space-Metric-Ab)
      ( metric-space-Metric-Ab)
      ( neg-Metric-Ab MG)
  is-isometry-neg-Metric-Ab d x y =
    ( is-short-map-neg-Metric-Ab d x y ,
      reflects-neighborhoods-neg-Metric-Ab d x y)

  isometry-neg-Metric-Ab :
    isometry-Metric-Space
      ( metric-space-Metric-Ab)
      ( metric-space-Metric-Ab)
  isometry-neg-Metric-Ab = (neg-Metric-Ab MG , is-isometry-neg-Metric-Ab)
```

## Properties

### Addition is a modulated uniformly continuous map from the product metric space of a metric abelian group to the metric space

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where

  modulated-uniformly-continuous-map-add-pair-Metric-Ab :
    modulated-ucont-map-Metric-Space
      ( product-Metric-Space
        ( metric-space-Metric-Ab G)
        ( metric-space-Metric-Ab G))
      ( metric-space-Metric-Ab G)
  modulated-uniformly-continuous-map-add-pair-Metric-Ab =
    modulated-ucont-uncurry-map-is-binary-isometry-Metric-Space
      ( metric-space-Metric-Ab G)
      ( metric-space-Metric-Ab G)
      ( metric-space-Metric-Ab G)
      ( add-Metric-Ab G)
      ( is-isometry-add-Metric-Ab G)
      ( is-isometry-add-Metric-Ab' G)

  uniformly-continuous-map-add-pair-Metric-Ab :
    uniformly-continuous-map-Metric-Space
      ( product-Metric-Space
        ( metric-space-Metric-Ab G)
        ( metric-space-Metric-Ab G))
      ( metric-space-Metric-Ab G)
  uniformly-continuous-map-add-pair-Metric-Ab =
    uniformly-continuous-map-modulated-ucont-map-Metric-Space
      ( product-Metric-Space
        ( metric-space-Metric-Ab G)
        ( metric-space-Metric-Ab G))
      ( metric-space-Metric-Ab G)
      ( modulated-uniformly-continuous-map-add-pair-Metric-Ab)
```

### Neighborhoods of sums in metric abelian groups

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  (dxx' dyy' : ℚ⁺)
  (x x' y y' : type-Metric-Ab G)
  where abstract

  neighborhood-add-Metric-Ab :
    neighborhood-Metric-Ab G dxx' x x' →
    neighborhood-Metric-Ab G dyy' y y' →
    neighborhood-Metric-Ab G
      ( dxx' +ℚ⁺ dyy')
      ( add-Metric-Ab G x y)
      ( add-Metric-Ab G x' y')
  neighborhood-add-Metric-Ab Nxx' Nyy' =
    triangular-neighborhood-Metric-Ab G
      ( add-Metric-Ab G x y)
      ( add-Metric-Ab G x' y)
      ( add-Metric-Ab G x' y')
      ( dxx')
      ( dyy')
      ( forward-implication
        ( is-isometry-add-Metric-Ab G x' dyy' y y')
        ( Nyy'))
      ( forward-implication
        ( is-isometry-add-Metric-Ab' G y dxx' x x')
        ( Nxx'))
```
