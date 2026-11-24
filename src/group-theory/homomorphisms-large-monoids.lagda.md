# Homomorphisms of large monoids

```agda
module group-theory.homomorphisms-large-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.similarity-preserving-maps-cumulative-large-sets
open import foundation.universe-levels

open import group-theory.homomorphisms-large-semigroups
open import group-theory.homomorphisms-monoids
open import group-theory.large-monoids
```

</details>

## Idea

A
{{#concept "homomorphism" Disambiguation="of large monoids" Agda=hom-Large-Monoid}}
from a [large monoid](group-theory.large-monoids.md) `M` to a large monoid `N`
is a [homomorphism](group-theory.homomorphisms-large-semigroups.md) of their
underlying [large semigroups](group-theory.large-semigroups.md) that preserves
the unit.

## Definition

```agda
record
  hom-Large-Monoid
    {α β : Level → Level}
    {γ δ : Level → Level → Level}
    (M : Large-Monoid α γ)
    (N : Large-Monoid β δ) :
    UUω
  where

  constructor
    make-hom-Large-Monoid

  field
    hom-large-semigroup-hom-Large-Monoid :
      hom-Large-Semigroup
        ( large-semigroup-Large-Monoid M)
        ( large-semigroup-Large-Monoid N)

  sim-preserving-map-hom-Large-Monoid :
    sim-preserving-map-Cumulative-Large-Set
      ( id)
      ( cumulative-large-set-Large-Monoid M)
      ( cumulative-large-set-Large-Monoid N)
  sim-preserving-map-hom-Large-Monoid =
    sim-preserving-map-hom-Large-Semigroup
      ( hom-large-semigroup-hom-Large-Monoid)

  map-hom-Large-Monoid :
    {l : Level} → type-Large-Monoid M l → type-Large-Monoid N l
  map-hom-Large-Monoid =
    map-hom-Large-Semigroup hom-large-semigroup-hom-Large-Monoid

  field
    preserves-unit-hom-Large-Monoid :
      map-hom-Large-Monoid (unit-Large-Monoid M) ＝ unit-Large-Monoid N

  preserves-mul-hom-Large-Monoid :
    {l1 l2 : Level} {x : type-Large-Monoid M l1} {y : type-Large-Monoid M l2} →
    map-hom-Large-Monoid (mul-Large-Monoid M x y) ＝
    mul-Large-Monoid N (map-hom-Large-Monoid x) (map-hom-Large-Monoid y)
  preserves-mul-hom-Large-Monoid =
    preserves-mul-hom-Large-Semigroup hom-large-semigroup-hom-Large-Monoid

open hom-Large-Monoid public
```

## Properties

### Monoid homomorphisms preserve raised units

```agda
module _
  {α β : Level → Level}
  {γ δ : Level → Level → Level}
  {M : Large-Monoid α γ}
  {N : Large-Monoid β δ}
  (f : hom-Large-Monoid M N)
  where abstract

  preserves-raise-unit-hom-Large-Monoid :
    (l : Level) →
    map-hom-Large-Monoid f (raise-unit-Large-Monoid M l) ＝
    raise-unit-Large-Monoid N l
  preserves-raise-unit-hom-Large-Monoid l =
    commute-map-raise-sim-preserving-map-Cumulative-Large-Set
      ( cumulative-large-set-Large-Monoid M)
      ( cumulative-large-set-Large-Monoid N)
      ( sim-preserving-map-hom-Large-Monoid f)
      ( l)
      ( unit-Large-Monoid M) ∙
    ( ap (raise-Large-Monoid N l) (preserves-unit-hom-Large-Monoid f))
```

### Small monoid homomorphisms from large ones

```agda
module _
  {α β : Level → Level}
  {γ δ : Level → Level → Level}
  {M : Large-Monoid α γ}
  {N : Large-Monoid β δ}
  (f : hom-Large-Monoid M N)
  where

  hom-monoid-hom-Large-Monoid :
    (l : Level) →
    hom-Monoid (monoid-Large-Monoid M l) (monoid-Large-Monoid N l)
  hom-monoid-hom-Large-Monoid l =
    ( hom-semigroup-hom-Large-Semigroup
        ( hom-large-semigroup-hom-Large-Monoid f)
        ( l) ,
      preserves-raise-unit-hom-Large-Monoid f l)
```
