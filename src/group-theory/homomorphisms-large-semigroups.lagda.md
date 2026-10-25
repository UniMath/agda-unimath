# Homomorphisms of large semigroups

```agda
module group-theory.homomorphisms-large-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.similarity-preserving-maps-cumulative-large-sets
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups
open import group-theory.large-semigroups
```

</details>

## Idea

Given two [large semigroups](group-theory.large-semigroups.md) `G` and `H`, a
{{#concept "semigroup homomorphism" Disambiguation="large semigroup" Agda=hom-Large-Semigroup}}
from `G` to `H` is a
[similarity-preserving map](foundation.similarity-preserving-maps-cumulative-large-sets.md)
from `G` to `H` that preserves multiplication.

## Definition

```agda
record
  hom-Large-Semigroup
    { α γ : Level → Level}
    { β δ : Level → Level → Level}
    ( G : Large-Semigroup α β)
    ( H : Large-Semigroup γ δ) :
    UUω
    where

  constructor
    make-hom-Large-Semigroup

  field
    sim-preserving-map-hom-Large-Semigroup :
      sim-preserving-map-Cumulative-Large-Set
        ( id)
        ( cumulative-large-set-Large-Semigroup G)
        ( cumulative-large-set-Large-Semigroup H)

  map-hom-Large-Semigroup :
    {l : Level} → type-Large-Semigroup G l → type-Large-Semigroup H l
  map-hom-Large-Semigroup =
    map-sim-preserving-map-Cumulative-Large-Set
      ( cumulative-large-set-Large-Semigroup G)
      ( cumulative-large-set-Large-Semigroup H)
      ( sim-preserving-map-hom-Large-Semigroup)

  field
    preserves-mul-hom-Large-Semigroup :
      {l1 l2 : Level} →
      {x : type-Large-Semigroup G l1} {y : type-Large-Semigroup G l2} →
      map-hom-Large-Semigroup (mul-Large-Semigroup G x y) ＝
      mul-Large-Semigroup H
        ( map-hom-Large-Semigroup x)
        ( map-hom-Large-Semigroup y)

open hom-Large-Semigroup public
```

## Properties

### Homomorphisms on small semigroups from homomorphisms on large semigroups

```agda
module _
  { α γ : Level → Level}
  { β δ : Level → Level → Level}
  { G : Large-Semigroup α β}
  { H : Large-Semigroup γ δ}
  (f : hom-Large-Semigroup G H)
  where

  hom-semigroup-hom-Large-Semigroup :
    (l : Level) →
    hom-Semigroup
      ( semigroup-Large-Semigroup G l)
      ( semigroup-Large-Semigroup H l)
  hom-semigroup-hom-Large-Semigroup l =
    ( map-hom-Large-Semigroup f ,
      preserves-mul-hom-Large-Semigroup f)
```
