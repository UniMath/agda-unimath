# Finite commutative monoids

```agda
module finite-group-theory.finite-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import finite-group-theory.finite-monoids

open import foundation.identity-types
open import foundation.sets
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups

open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

A {{#concept "finite commutative monoid" Agda=Finite-Commutative-Monoid}} is a
[finite monoid](finite-group-theory.finite-monoids.md) `M` in which `xy = yx`
holds for all `x y : M`.

## Definition

### Finite commutative monoids

```agda
is-commutative-Finite-Monoid :
  {l : Level} (M : Finite-Monoid l) → UU l
is-commutative-Finite-Monoid M =
  is-commutative-Monoid (monoid-Finite-Monoid M)

Finite-Commutative-Monoid : (l : Level) → UU (lsuc l)
Finite-Commutative-Monoid l = Σ (Finite-Monoid l) is-commutative-Finite-Monoid

module _
  {l : Level} (M : Finite-Commutative-Monoid l)
  where

  finite-monoid-Finite-Commutative-Monoid : Finite-Monoid l
  finite-monoid-Finite-Commutative-Monoid = pr1 M

  monoid-Finite-Commutative-Monoid : Monoid l
  monoid-Finite-Commutative-Monoid =
    monoid-Finite-Monoid finite-monoid-Finite-Commutative-Monoid

  finite-type-Finite-Commutative-Monoid : Finite-Type l
  finite-type-Finite-Commutative-Monoid =
    finite-type-Finite-Monoid finite-monoid-Finite-Commutative-Monoid

  type-Finite-Commutative-Monoid : UU l
  type-Finite-Commutative-Monoid =
    type-Finite-Monoid finite-monoid-Finite-Commutative-Monoid

  is-finite-type-Finite-Commutative-Monoid :
    is-finite type-Finite-Commutative-Monoid
  is-finite-type-Finite-Commutative-Monoid =
    is-finite-type-Finite-Monoid finite-monoid-Finite-Commutative-Monoid

  semigroup-Finite-Commutative-Monoid : Semigroup l
  semigroup-Finite-Commutative-Monoid =
    semigroup-Finite-Monoid finite-monoid-Finite-Commutative-Monoid

  set-Finite-Commutative-Monoid : Set l
  set-Finite-Commutative-Monoid =
    set-Finite-Monoid finite-monoid-Finite-Commutative-Monoid

  is-set-type-Finite-Commutative-Monoid : is-set type-Finite-Commutative-Monoid
  is-set-type-Finite-Commutative-Monoid =
    is-set-type-Finite-Monoid finite-monoid-Finite-Commutative-Monoid
```

### The multiplicative operation of a commutative monoid

```agda
  has-associative-mul-Finite-Commutative-Monoid :
    has-associative-mul-Set set-Finite-Commutative-Monoid
  has-associative-mul-Finite-Commutative-Monoid =
    has-associative-mul-Semigroup semigroup-Finite-Commutative-Monoid

  mul-Finite-Commutative-Monoid :
    (x y : type-Finite-Commutative-Monoid) → type-Finite-Commutative-Monoid
  mul-Finite-Commutative-Monoid =
    mul-Finite-Monoid finite-monoid-Finite-Commutative-Monoid

  mul-Finite-Commutative-Monoid' :
    (x y : type-Finite-Commutative-Monoid) → type-Finite-Commutative-Monoid
  mul-Finite-Commutative-Monoid' =
    mul-Finite-Monoid' finite-monoid-Finite-Commutative-Monoid

  ap-mul-Finite-Commutative-Monoid :
    {x x' y y' : type-Finite-Commutative-Monoid} →
    x ＝ x' → y ＝ y' →
    mul-Finite-Commutative-Monoid x y ＝ mul-Finite-Commutative-Monoid x' y'
  ap-mul-Finite-Commutative-Monoid =
    ap-mul-Finite-Monoid finite-monoid-Finite-Commutative-Monoid

  associative-mul-Finite-Commutative-Monoid :
    (x y z : type-Finite-Commutative-Monoid) →
    ( mul-Finite-Commutative-Monoid (mul-Finite-Commutative-Monoid x y) z) ＝
    ( mul-Finite-Commutative-Monoid x (mul-Finite-Commutative-Monoid y z))
  associative-mul-Finite-Commutative-Monoid =
    associative-mul-Finite-Monoid finite-monoid-Finite-Commutative-Monoid

  commutative-mul-Finite-Commutative-Monoid :
    (x y : type-Finite-Commutative-Monoid) →
    mul-Finite-Commutative-Monoid x y ＝ mul-Finite-Commutative-Monoid y x
  commutative-mul-Finite-Commutative-Monoid = pr2 M

  commutative-monoid-Finite-Commutative-Monoid : Commutative-Monoid l
  pr1 commutative-monoid-Finite-Commutative-Monoid =
    monoid-Finite-Commutative-Monoid
  pr2 commutative-monoid-Finite-Commutative-Monoid =
    commutative-mul-Finite-Commutative-Monoid

  interchange-mul-mul-Finite-Commutative-Monoid :
    (x y x' y' : type-Finite-Commutative-Monoid) →
    ( mul-Finite-Commutative-Monoid
      ( mul-Finite-Commutative-Monoid x y)
      ( mul-Finite-Commutative-Monoid x' y')) ＝
    ( mul-Finite-Commutative-Monoid
      ( mul-Finite-Commutative-Monoid x x')
      ( mul-Finite-Commutative-Monoid y y'))
  interchange-mul-mul-Finite-Commutative-Monoid =
    interchange-mul-mul-Commutative-Monoid
      commutative-monoid-Finite-Commutative-Monoid

  right-swap-mul-Finite-Commutative-Monoid :
    (x y z : type-Finite-Commutative-Monoid) →
    mul-Finite-Commutative-Monoid (mul-Finite-Commutative-Monoid x y) z ＝
    mul-Finite-Commutative-Monoid (mul-Finite-Commutative-Monoid x z) y
  right-swap-mul-Finite-Commutative-Monoid =
    right-swap-mul-Commutative-Monoid
      commutative-monoid-Finite-Commutative-Monoid

  left-swap-mul-Finite-Commutative-Monoid :
    (x y z : type-Finite-Commutative-Monoid) →
    mul-Finite-Commutative-Monoid x (mul-Finite-Commutative-Monoid y z) ＝
    mul-Finite-Commutative-Monoid y (mul-Finite-Commutative-Monoid x z)
  left-swap-mul-Finite-Commutative-Monoid =
    left-swap-mul-Commutative-Monoid
      commutative-monoid-Finite-Commutative-Monoid
```

### The unit element of a commutative monoid

```agda
module _
  {l : Level} (M : Finite-Commutative-Monoid l)
  where

  has-unit-Finite-Commutative-Monoid :
    is-unital (mul-Finite-Commutative-Monoid M)
  has-unit-Finite-Commutative-Monoid =
    has-unit-Monoid (monoid-Finite-Commutative-Monoid M)

  unit-Finite-Commutative-Monoid : type-Finite-Commutative-Monoid M
  unit-Finite-Commutative-Monoid =
    unit-Monoid (monoid-Finite-Commutative-Monoid M)

  left-unit-law-mul-Finite-Commutative-Monoid :
    (x : type-Finite-Commutative-Monoid M) →
    mul-Finite-Commutative-Monoid M unit-Finite-Commutative-Monoid x ＝ x
  left-unit-law-mul-Finite-Commutative-Monoid =
    left-unit-law-mul-Monoid (monoid-Finite-Commutative-Monoid M)

  right-unit-law-mul-Finite-Commutative-Monoid :
    (x : type-Finite-Commutative-Monoid M) →
    mul-Finite-Commutative-Monoid M x unit-Finite-Commutative-Monoid ＝ x
  right-unit-law-mul-Finite-Commutative-Monoid =
    right-unit-law-mul-Monoid (monoid-Finite-Commutative-Monoid M)
```

## Properties

### There is a finite number of ways to equip a finite type with the structure of a finite commutative monoid

```agda
module _
  {l : Level}
  (X : Finite-Type l)
  where

  structure-commutative-monoid-Finite-Type : UU l
  structure-commutative-monoid-Finite-Type =
    Σ ( structure-monoid-Finite-Type X)
      ( λ m →
        is-commutative-Finite-Monoid
          ( finite-monoid-structure-monoid-Finite-Type X m))

  finite-commutative-monoid-structure-commutative-monoid-Finite-Type :
    structure-commutative-monoid-Finite-Type → Finite-Commutative-Monoid l
  finite-commutative-monoid-structure-commutative-monoid-Finite-Type (m , c) =
    finite-monoid-structure-monoid-Finite-Type X m , c

  is-finite-structure-commutative-monoid-Finite-Type :
    is-finite structure-commutative-monoid-Finite-Type
  is-finite-structure-commutative-monoid-Finite-Type =
    is-finite-Σ
      ( is-finite-structure-monoid-Finite-Type X)
      ( λ m →
        is-finite-Π
          ( is-finite-type-Finite-Type X)
          ( λ x →
            is-finite-Π
              ( is-finite-type-Finite-Type X)
              ( λ y → is-finite-eq-Finite-Type X)))
```
