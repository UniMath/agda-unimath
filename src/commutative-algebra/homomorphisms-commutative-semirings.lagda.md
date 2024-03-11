# Homomorphisms of commutative semirings

```agda
module commutative-algebra.homomorphisms-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import foundation.equivalences
open import foundation.identity-types
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.homomorphisms-commutative-monoids
open import group-theory.homomorphisms-monoids

open import ring-theory.homomorphisms-semirings
```

</details>

## Idea

A **homomorphism of commutative semirings** is a map which preserves `0`, `+`,
`1`, and `·`.

## Definitions

```agda
module _
  {l1 l2 : Level} (A : Commutative-Semiring l1) (B : Commutative-Semiring l2)
  where

  hom-set-Commutative-Semiring : Set (l1 ⊔ l2)
  hom-set-Commutative-Semiring =
    hom-set-Semiring
      ( semiring-Commutative-Semiring A)
      ( semiring-Commutative-Semiring B)

  hom-Commutative-Semiring : UU (l1 ⊔ l2)
  hom-Commutative-Semiring =
    hom-Semiring
      ( semiring-Commutative-Semiring A)
      ( semiring-Commutative-Semiring B)

  is-set-hom-Commutative-Semiring : is-set hom-Commutative-Semiring
  is-set-hom-Commutative-Semiring =
    is-set-hom-Semiring
      ( semiring-Commutative-Semiring A)
      ( semiring-Commutative-Semiring B)

  module _
    (f : hom-Commutative-Semiring)
    where

    hom-additive-commutative-monoid-hom-Commutative-Semiring :
      hom-Commutative-Monoid
        ( additive-commutative-monoid-Commutative-Semiring A)
        ( additive-commutative-monoid-Commutative-Semiring B)
    hom-additive-commutative-monoid-hom-Commutative-Semiring =
      hom-additive-commutative-monoid-hom-Semiring
        ( semiring-Commutative-Semiring A)
        ( semiring-Commutative-Semiring B)
        ( f)

    map-hom-Commutative-Semiring :
      type-Commutative-Semiring A → type-Commutative-Semiring B
    map-hom-Commutative-Semiring =
      map-hom-Semiring
        ( semiring-Commutative-Semiring A)
        ( semiring-Commutative-Semiring B)
        ( f)

    preserves-addition-hom-Commutative-Semiring :
      {x y : type-Commutative-Semiring A} →
      map-hom-Commutative-Semiring (add-Commutative-Semiring A x y) ＝
      add-Commutative-Semiring B
        ( map-hom-Commutative-Semiring x)
        ( map-hom-Commutative-Semiring y)
    preserves-addition-hom-Commutative-Semiring =
      preserves-addition-hom-Semiring
        ( semiring-Commutative-Semiring A)
        ( semiring-Commutative-Semiring B)
        ( f)

    preserves-zero-hom-Commutative-Semiring :
      map-hom-Commutative-Semiring (zero-Commutative-Semiring A) ＝
      zero-Commutative-Semiring B
    preserves-zero-hom-Commutative-Semiring =
      preserves-zero-hom-Semiring
        ( semiring-Commutative-Semiring A)
        ( semiring-Commutative-Semiring B)
        ( f)

    preserves-mul-hom-Commutative-Semiring :
      {x y : type-Commutative-Semiring A} →
      map-hom-Commutative-Semiring (mul-Commutative-Semiring A x y) ＝
      mul-Commutative-Semiring B
        ( map-hom-Commutative-Semiring x)
        ( map-hom-Commutative-Semiring y)
    preserves-mul-hom-Commutative-Semiring =
      preserves-mul-hom-Semiring
        ( semiring-Commutative-Semiring A)
        ( semiring-Commutative-Semiring B)
        ( f)

    preserves-unit-hom-Commutative-Semiring :
      map-hom-Commutative-Semiring (one-Commutative-Semiring A) ＝
      one-Commutative-Semiring B
    preserves-unit-hom-Commutative-Semiring =
      preserves-unit-hom-Semiring
        ( semiring-Commutative-Semiring A)
        ( semiring-Commutative-Semiring B)
        ( f)

    is-homomorphism-semiring-hom-Commutative-Semiring :
      is-homomorphism-semiring-hom-Commutative-Monoid
        ( semiring-Commutative-Semiring A)
        ( semiring-Commutative-Semiring B)
        ( hom-additive-commutative-monoid-hom-Commutative-Semiring)
    is-homomorphism-semiring-hom-Commutative-Semiring =
      is-homomorphism-semiring-hom-Semiring
        ( semiring-Commutative-Semiring A)
        ( semiring-Commutative-Semiring B)
        ( f)

    hom-multiplicative-monoid-hom-Commutative-Semiring :
      hom-Monoid
        ( multiplicative-monoid-Commutative-Semiring A)
        ( multiplicative-monoid-Commutative-Semiring B)
    hom-multiplicative-monoid-hom-Commutative-Semiring =
      hom-multiplicative-monoid-hom-Semiring
        ( semiring-Commutative-Semiring A)
        ( semiring-Commutative-Semiring B)
        ( f)
```

### The identity homomorphism of commutative semirings

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  hom-additive-commutative-monoid-id-hom-Commutative-Semiring :
    hom-Commutative-Monoid
      ( additive-commutative-monoid-Commutative-Semiring A)
      ( additive-commutative-monoid-Commutative-Semiring A)
  hom-additive-commutative-monoid-id-hom-Commutative-Semiring =
    hom-additive-commutative-monoid-id-hom-Semiring
      ( semiring-Commutative-Semiring A)

  preserves-mul-id-hom-Commutative-Semiring :
    {x y : type-Commutative-Semiring A} →
    mul-Commutative-Semiring A x y ＝ mul-Commutative-Semiring A x y
  preserves-mul-id-hom-Commutative-Semiring =
    preserves-mul-id-hom-Semiring (semiring-Commutative-Semiring A)

  preserves-unit-id-hom-Commutative-Semiring :
    one-Commutative-Semiring A ＝ one-Commutative-Semiring A
  preserves-unit-id-hom-Commutative-Semiring =
    preserves-unit-id-hom-Semiring (semiring-Commutative-Semiring A)

  id-hom-Commutative-Semiring : hom-Commutative-Semiring A A
  id-hom-Commutative-Semiring =
    id-hom-Semiring (semiring-Commutative-Semiring A)
```

### Composition of homomorphisms of commutative semirings

```agda
module _
  {l1 l2 l3 : Level}
  (A : Commutative-Semiring l1)
  (B : Commutative-Semiring l2)
  (C : Commutative-Semiring l3)
  (g : hom-Commutative-Semiring B C)
  (f : hom-Commutative-Semiring A B)
  where

  hom-additive-commutative-monoid-comp-hom-Commutative-Semiring :
    hom-Commutative-Monoid
      ( additive-commutative-monoid-Commutative-Semiring A)
      ( additive-commutative-monoid-Commutative-Semiring C)
  hom-additive-commutative-monoid-comp-hom-Commutative-Semiring =
    hom-additive-commutative-monoid-comp-hom-Semiring
      ( semiring-Commutative-Semiring A)
      ( semiring-Commutative-Semiring B)
      ( semiring-Commutative-Semiring C)
      ( g)
      ( f)

  hom-multiplicative-monoid-comp-hom-Commutative-Semiring :
    hom-Monoid
      ( multiplicative-monoid-Commutative-Semiring A)
      ( multiplicative-monoid-Commutative-Semiring C)
  hom-multiplicative-monoid-comp-hom-Commutative-Semiring =
    hom-multiplicative-monoid-comp-hom-Semiring
      ( semiring-Commutative-Semiring A)
      ( semiring-Commutative-Semiring B)
      ( semiring-Commutative-Semiring C)
      ( g)
      ( f)

  map-comp-hom-Commutative-Semiring :
    type-Commutative-Semiring A → type-Commutative-Semiring C
  map-comp-hom-Commutative-Semiring =
    map-comp-hom-Semiring
      ( semiring-Commutative-Semiring A)
      ( semiring-Commutative-Semiring B)
      ( semiring-Commutative-Semiring C)
      ( g)
      ( f)

  preserves-mul-comp-hom-Commutative-Semiring :
    {x y : type-Commutative-Semiring A} →
    map-comp-hom-Commutative-Semiring (mul-Commutative-Semiring A x y) ＝
    mul-Commutative-Semiring C
      ( map-comp-hom-Commutative-Semiring x)
      ( map-comp-hom-Commutative-Semiring y)
  preserves-mul-comp-hom-Commutative-Semiring =
    preserves-mul-comp-hom-Semiring
      ( semiring-Commutative-Semiring A)
      ( semiring-Commutative-Semiring B)
      ( semiring-Commutative-Semiring C)
      ( g)
      ( f)

  preserves-unit-comp-hom-Commutative-Semiring :
    map-comp-hom-Commutative-Semiring (one-Commutative-Semiring A) ＝
    one-Commutative-Semiring C
  preserves-unit-comp-hom-Commutative-Semiring =
    preserves-unit-comp-hom-Semiring
      ( semiring-Commutative-Semiring A)
      ( semiring-Commutative-Semiring B)
      ( semiring-Commutative-Semiring C)
      ( g)
      ( f)

  comp-hom-Commutative-Semiring : hom-Commutative-Semiring A C
  comp-hom-Commutative-Semiring =
    comp-hom-Semiring
      ( semiring-Commutative-Semiring A)
      ( semiring-Commutative-Semiring B)
      ( semiring-Commutative-Semiring C)
      ( g)
      ( f)
```

### Homotopies of homomorphisms of commutative semirings

```agda
module _
  {l1 l2 : Level} (R : Commutative-Semiring l1) (S : Commutative-Semiring l2)
  where

  htpy-hom-Commutative-Semiring :
    (f g : hom-Commutative-Semiring R S) → UU (l1 ⊔ l2)
  htpy-hom-Commutative-Semiring f g =
    htpy-hom-Commutative-Monoid
      ( additive-commutative-monoid-Commutative-Semiring R)
      ( additive-commutative-monoid-Commutative-Semiring S)
      ( hom-additive-commutative-monoid-hom-Commutative-Semiring R S f)
      ( hom-additive-commutative-monoid-hom-Commutative-Semiring R S g)

  refl-htpy-hom-Commutative-Semiring :
    (f : hom-Commutative-Semiring R S) → htpy-hom-Commutative-Semiring f f
  refl-htpy-hom-Commutative-Semiring f =
    refl-htpy-hom-Commutative-Monoid
      ( additive-commutative-monoid-Commutative-Semiring R)
      ( additive-commutative-monoid-Commutative-Semiring S)
      ( hom-additive-commutative-monoid-hom-Commutative-Semiring R S f)
```

## Properties

### Homotopies characterize identifications of homomorphisms of commutative semirings

```agda
module _
  {l1 l2 : Level} (A : Commutative-Semiring l1) (B : Commutative-Semiring l2)
  (f : hom-Commutative-Semiring A B)
  where

  is-torsorial-htpy-hom-Commutative-Semiring :
    is-torsorial (htpy-hom-Commutative-Semiring A B f)
  is-torsorial-htpy-hom-Commutative-Semiring =
    is-torsorial-htpy-hom-Semiring
      ( semiring-Commutative-Semiring A)
      ( semiring-Commutative-Semiring B)
      ( f)

  htpy-eq-hom-Commutative-Semiring :
    (g : hom-Commutative-Semiring A B) →
    (f ＝ g) → htpy-hom-Commutative-Semiring A B f g
  htpy-eq-hom-Commutative-Semiring =
    htpy-eq-hom-Semiring
      ( semiring-Commutative-Semiring A)
      ( semiring-Commutative-Semiring B)
      ( f)

  is-equiv-htpy-eq-hom-Commutative-Semiring :
    (g : hom-Commutative-Semiring A B) →
    is-equiv (htpy-eq-hom-Commutative-Semiring g)
  is-equiv-htpy-eq-hom-Commutative-Semiring =
    is-equiv-htpy-eq-hom-Semiring
      ( semiring-Commutative-Semiring A)
      ( semiring-Commutative-Semiring B)
      ( f)

  extensionality-hom-Commutative-Semiring :
    (g : hom-Commutative-Semiring A B) →
    (f ＝ g) ≃ htpy-hom-Commutative-Semiring A B f g
  extensionality-hom-Commutative-Semiring =
    extensionality-hom-Semiring
      ( semiring-Commutative-Semiring A)
      ( semiring-Commutative-Semiring B)
      ( f)

  eq-htpy-hom-Commutative-Semiring :
    (g : hom-Commutative-Semiring A B) →
    htpy-hom-Commutative-Semiring A B f g → f ＝ g
  eq-htpy-hom-Commutative-Semiring =
    eq-htpy-hom-Semiring
      ( semiring-Commutative-Semiring A)
      ( semiring-Commutative-Semiring B)
      ( f)
```

### Associativity of composition of homomorphisms of commutative semirings

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Commutative-Semiring l1)
  (B : Commutative-Semiring l2)
  (C : Commutative-Semiring l3)
  (D : Commutative-Semiring l4)
  (h : hom-Commutative-Semiring C D)
  (g : hom-Commutative-Semiring B C)
  (f : hom-Commutative-Semiring A B)
  where

  associative-comp-hom-Commutative-Semiring :
    comp-hom-Commutative-Semiring A B D
      ( comp-hom-Commutative-Semiring B C D h g)
      ( f) ＝
    comp-hom-Commutative-Semiring A C D
      ( h)
      ( comp-hom-Commutative-Semiring A B C g f)
  associative-comp-hom-Commutative-Semiring =
    associative-comp-hom-Semiring
      ( semiring-Commutative-Semiring A)
      ( semiring-Commutative-Semiring B)
      ( semiring-Commutative-Semiring C)
      ( semiring-Commutative-Semiring D)
      ( h)
      ( g)
      ( f)
```

### Unit laws for composition of homomorphisms of commutative semirings

```agda
module _
  {l1 l2 : Level} (A : Commutative-Semiring l1) (B : Commutative-Semiring l2)
  (f : hom-Commutative-Semiring A B)
  where

  left-unit-law-comp-hom-Commutative-Semiring :
    comp-hom-Commutative-Semiring A B B (id-hom-Commutative-Semiring B) f ＝ f
  left-unit-law-comp-hom-Commutative-Semiring =
    left-unit-law-comp-hom-Semiring
      ( semiring-Commutative-Semiring A)
      ( semiring-Commutative-Semiring B)
      ( f)

  right-unit-law-comp-hom-Commutative-Semiring :
    comp-hom-Commutative-Semiring A A B f (id-hom-Commutative-Semiring A) ＝ f
  right-unit-law-comp-hom-Commutative-Semiring =
    right-unit-law-comp-hom-Semiring
      ( semiring-Commutative-Semiring A)
      ( semiring-Commutative-Semiring B)
      ( f)
```
