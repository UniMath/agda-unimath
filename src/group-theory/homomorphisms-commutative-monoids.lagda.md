# Homomorphisms of commutative monoids

```agda
module group-theory.homomorphisms-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.sets
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.homomorphisms-monoids
open import group-theory.homomorphisms-semigroups
```

</details>

## Idea

Homomorphisms between two commutative monoids are homomorphisms between their
underlying monoids.

## Definition

### Homomorphisms of commutative monoids

```agda
module _
  {l1 l2 : Level} (M1 : Commutative-Monoid l1) (M2 : Commutative-Monoid l2)
  where

  hom-Commutative-Monoid : Set (l1 ⊔ l2)
  hom-Commutative-Monoid =
    hom-Monoid (monoid-Commutative-Monoid M1) (monoid-Commutative-Monoid M2)

  type-hom-Commutative-Monoid : UU (l1 ⊔ l2)
  type-hom-Commutative-Monoid =
    type-hom-Monoid
      ( monoid-Commutative-Monoid M1)
      ( monoid-Commutative-Monoid M2)

module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (N : Commutative-Monoid l2)
  (f : type-hom-Commutative-Monoid M N)
  where

  hom-semigroup-hom-Commutative-Monoid :
    type-hom-Semigroup
      ( semigroup-Commutative-Monoid M)
      ( semigroup-Commutative-Monoid N)
  hom-semigroup-hom-Commutative-Monoid =
    hom-semigroup-hom-Monoid
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)
      ( f)

  map-hom-Commutative-Monoid :
    type-Commutative-Monoid M → type-Commutative-Monoid N
  map-hom-Commutative-Monoid =
    map-hom-Monoid
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)
      ( f)

  preserves-mul-hom-Commutative-Monoid :
    preserves-mul-Semigroup
      ( semigroup-Commutative-Monoid M)
      ( semigroup-Commutative-Monoid N)
      ( map-hom-Commutative-Monoid)
  preserves-mul-hom-Commutative-Monoid =
    preserves-mul-hom-Monoid
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)
      ( f)

  preserves-unit-hom-Commutative-Monoid :
    preserves-unit-hom-Semigroup
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)
      ( hom-semigroup-hom-Commutative-Monoid)
  preserves-unit-hom-Commutative-Monoid =
    preserves-unit-hom-Monoid
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)
      ( f)
```

### The identity homomorphism of monoids

```agda
id-hom-Commutative-Monoid :
  {l : Level} (M : Commutative-Monoid l) → type-hom-Commutative-Monoid M M
id-hom-Commutative-Monoid M = id-hom-Monoid (monoid-Commutative-Monoid M)
```
