# Homomorphisms of monoids

```agda
module group-theory.homomorphisms-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups
open import group-theory.monoids
```

</details>

## Idea

Homomorphisms between two monoids are homomorphisms between their underlying semigroups that preserve the unit element.

## Definition

### Homomorphisms of monoids

```agda
preserves-unit-hom-Semigroup :
  { l1 l2 : Level} (M1 : Monoid l1) (M2 : Monoid l2) →
  ( type-hom-Semigroup (semigroup-Monoid M1) (semigroup-Monoid M2)) → UU l2
preserves-unit-hom-Semigroup M1 M2 f =
  Id ( map-hom-Semigroup
       ( semigroup-Monoid M1)
       ( semigroup-Monoid M2)
       ( f)
       ( unit-Monoid M1))
     ( unit-Monoid M2)

hom-Monoid :
  { l1 l2 : Level} (M1 : Monoid l1) (M2 : Monoid l2) → UU (l1 ⊔ l2)
hom-Monoid M1 M2 =
  Σ ( type-hom-Semigroup (semigroup-Monoid M1) (semigroup-Monoid M2))
    ( preserves-unit-hom-Semigroup M1 M2)

module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2) (f : hom-Monoid M N)
  where

  hom-semigroup-hom-Monoid :
    type-hom-Semigroup (semigroup-Monoid M) (semigroup-Monoid N)
  hom-semigroup-hom-Monoid = pr1 f

  map-hom-Monoid : type-Monoid M → type-Monoid N
  map-hom-Monoid =
    map-hom-Semigroup
      ( semigroup-Monoid M)
      ( semigroup-Monoid N)
      ( hom-semigroup-hom-Monoid)

  preserves-mul-hom-Monoid :
    preserves-mul-Semigroup
      ( semigroup-Monoid M)
      ( semigroup-Monoid N)
      ( map-hom-Monoid)
  preserves-mul-hom-Monoid =
    preserves-mul-hom-Semigroup
      ( semigroup-Monoid M)
      ( semigroup-Monoid N)
      ( hom-semigroup-hom-Monoid)

  preserves-unit-hom-Monoid :
    preserves-unit-hom-Semigroup M N hom-semigroup-hom-Monoid
  preserves-unit-hom-Monoid = pr2 f
```

### The identity homomorphism of monoids

```agda
preserves-unit-id-hom-Monoid :
  { l : Level} (M : Monoid l) →
  preserves-unit-hom-Semigroup M M (id-hom-Semigroup (semigroup-Monoid M))
preserves-unit-id-hom-Monoid M = refl

id-hom-Monoid :
  {l : Level} (M : Monoid l) → hom-Monoid M M
pr1 (id-hom-Monoid M) = id-hom-Semigroup (semigroup-Monoid M)
pr2 (id-hom-Monoid M) = preserves-unit-id-hom-Monoid M
```
