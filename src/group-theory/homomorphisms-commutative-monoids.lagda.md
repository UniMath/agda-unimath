# Homomorphisms of commutative monoids

```agda
module group-theory.homomorphisms-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.identity-types
open import foundation.sets
open import foundation.torsorial-type-families
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

  hom-set-Commutative-Monoid : Set (l1 ⊔ l2)
  hom-set-Commutative-Monoid =
    hom-set-Monoid (monoid-Commutative-Monoid M1) (monoid-Commutative-Monoid M2)

  hom-Commutative-Monoid : UU (l1 ⊔ l2)
  hom-Commutative-Monoid =
    hom-Monoid
      ( monoid-Commutative-Monoid M1)
      ( monoid-Commutative-Monoid M2)

module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (N : Commutative-Monoid l2)
  (f : hom-Commutative-Monoid M N)
  where

  hom-semigroup-hom-Commutative-Monoid :
    hom-Semigroup
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

### The identity homomorphism of commutative monoids

```agda
id-hom-Commutative-Monoid :
  {l : Level} (M : Commutative-Monoid l) → hom-Commutative-Monoid M M
id-hom-Commutative-Monoid M = id-hom-Monoid (monoid-Commutative-Monoid M)
```

### Composition of homomorphisms of commutative monoids

```agda
module _
  {l1 l2 l3 : Level}
  (K : Commutative-Monoid l1)
  (L : Commutative-Monoid l2)
  (M : Commutative-Monoid l3)
  where

  comp-hom-Commutative-Monoid :
    hom-Commutative-Monoid L M → hom-Commutative-Monoid K L →
    hom-Commutative-Monoid K M
  comp-hom-Commutative-Monoid =
    comp-hom-Monoid
      ( monoid-Commutative-Monoid K)
      ( monoid-Commutative-Monoid L)
      ( monoid-Commutative-Monoid M)
```

### Homotopies of homomorphisms of commutative monoids

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (N : Commutative-Monoid l2)
  where

  htpy-hom-Commutative-Monoid :
    (f g : hom-Commutative-Monoid M N) → UU (l1 ⊔ l2)
  htpy-hom-Commutative-Monoid =
    htpy-hom-Monoid
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)

  refl-htpy-hom-Commutative-Monoid :
    (f : hom-Commutative-Monoid M N) → htpy-hom-Commutative-Monoid f f
  refl-htpy-hom-Commutative-Monoid =
    refl-htpy-hom-Monoid
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)
```

## Properties

### Homotopies characterize identifications of homomorphisms of commutative monoids

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (N : Commutative-Monoid l2)
  (f : hom-Commutative-Monoid M N)
  where

  is-torsorial-htpy-hom-Commutative-Monoid :
    is-torsorial (htpy-hom-Commutative-Monoid M N f)
  is-torsorial-htpy-hom-Commutative-Monoid =
    is-torsorial-htpy-hom-Monoid
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)
      ( f)

  htpy-eq-hom-Commutative-Monoid :
    (g : hom-Commutative-Monoid M N) →
    (f ＝ g) → htpy-hom-Commutative-Monoid M N f g
  htpy-eq-hom-Commutative-Monoid =
    htpy-eq-hom-Monoid
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)
      ( f)

  is-equiv-htpy-eq-hom-Commutative-Monoid :
    (g : hom-Commutative-Monoid M N) →
    is-equiv (htpy-eq-hom-Commutative-Monoid g)
  is-equiv-htpy-eq-hom-Commutative-Monoid =
    is-equiv-htpy-eq-hom-Monoid
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)
      ( f)

  extensionality-hom-Commutative-Monoid :
    (g : hom-Commutative-Monoid M N) →
    (f ＝ g) ≃ htpy-hom-Commutative-Monoid M N f g
  extensionality-hom-Commutative-Monoid =
    extensionality-hom-Monoid
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)
      ( f)

  eq-htpy-hom-Commutative-Monoid :
    (g : hom-Commutative-Monoid M N) →
    htpy-hom-Commutative-Monoid M N f g → f ＝ g
  eq-htpy-hom-Commutative-Monoid =
    eq-htpy-hom-Monoid
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)
      ( f)
```

### Composition of homomorphisms of commutative monoids is associative

```agda
module _
  {l1 l2 l3 l4 : Level}
  (K : Commutative-Monoid l1)
  (L : Commutative-Monoid l2)
  (M : Commutative-Monoid l3)
  (N : Commutative-Monoid l4)
  where

  associative-comp-hom-Commutative-Monoid :
    (h : hom-Commutative-Monoid M N)
    (g : hom-Commutative-Monoid L M)
    (f : hom-Commutative-Monoid K L) →
    ( comp-hom-Commutative-Monoid K L N
      ( comp-hom-Commutative-Monoid L M N h g)
      ( f)) ＝
    ( comp-hom-Commutative-Monoid K M N
      ( h)
      ( comp-hom-Commutative-Monoid K L M g f))
  associative-comp-hom-Commutative-Monoid =
    associative-comp-hom-Monoid
      ( monoid-Commutative-Monoid K)
      ( monoid-Commutative-Monoid L)
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)
```

### The unit laws for composition of homomorphisms of commutative monoids

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (N : Commutative-Monoid l2)
  where

  left-unit-law-comp-hom-Commutative-Monoid :
    (f : hom-Commutative-Monoid M N) →
    comp-hom-Commutative-Monoid M N N (id-hom-Commutative-Monoid N) f ＝ f
  left-unit-law-comp-hom-Commutative-Monoid =
    left-unit-law-comp-hom-Monoid
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)

  right-unit-law-comp-hom-Commutative-Monoid :
    (f : hom-Commutative-Monoid M N) →
    comp-hom-Commutative-Monoid M M N f (id-hom-Commutative-Monoid M) ＝ f
  right-unit-law-comp-hom-Commutative-Monoid =
    right-unit-law-comp-hom-Monoid
      ( monoid-Commutative-Monoid M)
      ( monoid-Commutative-Monoid N)
```
