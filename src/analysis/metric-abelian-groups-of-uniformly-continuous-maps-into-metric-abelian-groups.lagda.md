# Metric abelian groups of uniformly continuous maps into metric abelian groups

```agda
module analysis.metric-abelian-groups-of-uniformly-continuous-maps-into-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import analysis.metric-abelian-groups

open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.function-abelian-groups
open import group-theory.subgroups-abelian-groups

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-space-of-uniformly-continuous-maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces
```

</details>

## Idea

Given a [metric space](metric-spaces.metric-spaces.md) `X` and a
[metric abelian group](analysis.metric-abelian-groups.md) `G`, the set of
[uniformly continuous maps](metric-spaces.uniformly-continuous-maps-metric-spaces.md)
from `X` to `G` itself forms a metric abelian group.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (G : Metric-Ab l3 l4)
  where

  abstract
    is-closed-under-negation-uniformly-continuous-map-Metric-Ab :
      is-closed-under-negatives-subset-Ab
        ( function-Ab (ab-Metric-Ab G) (type-Metric-Space X))
        ( is-uniformly-continuous-prop-map-Metric-Space
          ( X)
          ( metric-space-Metric-Ab G))
    is-closed-under-negation-uniformly-continuous-map-Metric-Ab =
      is-uniformly-continuous-map-comp-Metric-Space
        ( X)
        ( metric-space-Metric-Ab G)
        ( metric-space-Metric-Ab G)
        ( neg-Metric-Ab G)
        ( _)
        ( is-uniformly-continuous-map-is-isometry-Metric-Space
          ( metric-space-Metric-Ab G)
          ( metric-space-Metric-Ab G)
          ( neg-Metric-Ab G)
          ( is-isometry-neg-Metric-Ab G))

    is-closed-under-addition-uniformly-continuous-map-Metric-Ab :
      is-closed-under-addition-subset-Ab
        ( function-Ab (ab-Metric-Ab G) (type-Metric-Space X))
        ( is-uniformly-continuous-prop-map-Metric-Space
          ( X)
          ( metric-space-Metric-Ab G))
    is-closed-under-addition-uniformly-continuous-map-Metric-Ab
      {f} {g} ucont-f ucont-g =
      is-uniformly-continuous-map-uniformly-continuous-map-Metric-Space
        ( X)
        ( metric-space-Metric-Ab G)
        ( comp-uniformly-continuous-map-Metric-Space
          ( X)
          ( product-Metric-Space
            ( metric-space-Metric-Ab G)
            ( metric-space-Metric-Ab G))
          ( metric-space-Metric-Ab G)
          ( uniformly-continuous-map-add-pair-Metric-Ab G)
          ( comp-uniformly-continuous-map-Metric-Space
            ( X)
            ( product-Metric-Space X X)
            ( product-Metric-Space
              ( metric-space-Metric-Ab G)
              ( metric-space-Metric-Ab G))
            ( product-uniformly-continuous-map-Metric-Space
              ( X)
              ( metric-space-Metric-Ab G)
              ( X)
              ( metric-space-Metric-Ab G)
              ( f , ucont-f)
              ( g , ucont-g))
            ( uniformly-continuous-map-isometry-Metric-Space
              ( X)
              ( product-Metric-Space X X)
              ( diagonal-product-isometry-Metric-Space X))))

  subgroup-uniformly-continuous-map-Metric-Ab :
    Subgroup-Ab
      ( l1 ⊔ l2 ⊔ l4)
      ( function-Ab (ab-Metric-Ab G) (type-Metric-Space X))
  subgroup-uniformly-continuous-map-Metric-Ab =
    ( is-uniformly-continuous-prop-map-Metric-Space
        ( X)
        ( metric-space-Metric-Ab G) ,
      is-uniformly-continuous-map-const-map-Metric-Space
        ( X)
        ( metric-space-Metric-Ab G)
        ( zero-Metric-Ab G) ,
      is-closed-under-addition-uniformly-continuous-map-Metric-Ab ,
      is-closed-under-negation-uniformly-continuous-map-Metric-Ab)

  ab-uniformly-continuous-map-Metric-Ab : Ab (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  ab-uniformly-continuous-map-Metric-Ab =
    ab-Subgroup-Ab
      ( function-Ab (ab-Metric-Ab G) (type-Metric-Space X))
      ( subgroup-uniformly-continuous-map-Metric-Ab)

  type-uniformly-continuous-map-Metric-Ab : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  type-uniformly-continuous-map-Metric-Ab =
    type-Ab ab-uniformly-continuous-map-Metric-Ab

  metric-space-uniformly-continuous-map-Metric-Ab :
    Metric-Space (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l4)
  metric-space-uniformly-continuous-map-Metric-Ab =
    metric-space-of-uniformly-continuous-maps-Metric-Space
      ( X)
      ( metric-space-Metric-Ab G)

  pseudometric-structure-uniformly-continuous-map-Metric-Ab :
    Pseudometric-Structure
      ( l1 ⊔ l4)
      ( type-uniformly-continuous-map-Metric-Ab)
  pseudometric-structure-uniformly-continuous-map-Metric-Ab =
    pseudometric-structure-Metric-Space
      ( metric-space-uniformly-continuous-map-Metric-Ab)

  neg-uniformly-continuous-map-Metric-Ab :
    type-uniformly-continuous-map-Metric-Ab →
    type-uniformly-continuous-map-Metric-Ab
  neg-uniformly-continuous-map-Metric-Ab =
    neg-Ab ab-uniformly-continuous-map-Metric-Ab

  add-uniformly-continuous-map-Metric-Ab :
    type-uniformly-continuous-map-Metric-Ab →
    type-uniformly-continuous-map-Metric-Ab →
    type-uniformly-continuous-map-Metric-Ab
  add-uniformly-continuous-map-Metric-Ab =
    add-Ab ab-uniformly-continuous-map-Metric-Ab

  abstract
    is-isometry-neg-uniformly-continuous-map-Metric-Ab :
      is-isometry-Metric-Space
        ( metric-space-uniformly-continuous-map-Metric-Ab)
        ( metric-space-uniformly-continuous-map-Metric-Ab)
        ( neg-uniformly-continuous-map-Metric-Ab)
    is-isometry-neg-uniformly-continuous-map-Metric-Ab
      d f@(map-f , _) g@(map-g , _) =
      iff-Π-iff-family
        ( λ x → is-isometry-neg-Metric-Ab G d (map-f x) (map-g x))

    is-isometry-add-uniformly-continuous-map-Metric-Ab :
      (f : type-uniformly-continuous-map-Metric-Ab) →
      is-isometry-Metric-Space
        ( metric-space-uniformly-continuous-map-Metric-Ab)
        ( metric-space-uniformly-continuous-map-Metric-Ab)
        ( add-uniformly-continuous-map-Metric-Ab f)
    is-isometry-add-uniformly-continuous-map-Metric-Ab
      (map-f , _) d (map-g , _) (map-h , _) =
      iff-Π-iff-family
        ( λ x → is-isometry-add-Metric-Ab G (map-f x) d (map-g x) (map-h x))

  metric-ab-uniformly-continuous-map-Metric-Ab :
    Metric-Ab (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l4)
  metric-ab-uniformly-continuous-map-Metric-Ab =
    ( ab-uniformly-continuous-map-Metric-Ab ,
      pseudometric-structure-uniformly-continuous-map-Metric-Ab ,
      is-extensional-pseudometric-Metric-Space
        ( metric-space-uniformly-continuous-map-Metric-Ab) ,
      is-isometry-neg-uniformly-continuous-map-Metric-Ab ,
      is-isometry-add-uniformly-continuous-map-Metric-Ab)
```
