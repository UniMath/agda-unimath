# Idempotent monoids

```agda
module group-theory.idempotent-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.bands
open import group-theory.monoids
open import group-theory.semigroups

open import structured-types.magmas
```

</details>

## Idea

An {{#concept "idempotent monoid" Agda=Idempotent-Monoid}} is a [monoid](group-theory.monoids.md) in which every element is [idempotent](group-theory.idempotent-elements-monoids.md).

## Definitions

### The predicate of being an idempotent monoid

```agda
module _
  {l1 : Level} (M : Monoid l1)
  where

  is-idempotent-Monoid : UU l1
  is-idempotent-Monoid = is-band-Semigroup (semigroup-Monoid M)

  is-prop-is-idempotent-Monoid :
    is-prop is-idempotent-Monoid
  is-prop-is-idempotent-Monoid =
    is-prop-is-band-Semigroup (semigroup-Monoid M)

  is-idempotent-prop-Monoid :
    Prop l1
  is-idempotent-prop-Monoid =
    is-band-prop-Semigroup (semigroup-Monoid M)
```

### The type of idempotent monoids

```agda
Idempotent-Monoid : (l : Level) → UU (lsuc l)
Idempotent-Monoid l = Σ (Monoid l) is-idempotent-Monoid

module _
  {l1 : Level} (M : Idempotent-Monoid l1)
  where

  monoid-Idempotent-Monoid : Monoid l1
  monoid-Idempotent-Monoid = pr1 M

  is-idempotent-Idempotent-Monoid :
    is-idempotent-Monoid monoid-Idempotent-Monoid
  is-idempotent-Idempotent-Monoid = pr2 M

  semigroup-Idempotent-Monoid : Semigroup l1
  semigroup-Idempotent-Monoid =
    semigroup-Monoid monoid-Idempotent-Monoid

  band-Idempotent-Monoid : Band l1
  pr1 band-Idempotent-Monoid = semigroup-Idempotent-Monoid
  pr2 band-Idempotent-Monoid = is-idempotent-Idempotent-Monoid

  set-Idempotent-Monoid : Set l1
  set-Idempotent-Monoid = set-Band band-Idempotent-Monoid

  type-Idempotent-Monoid : UU l1
  type-Idempotent-Monoid = type-Band band-Idempotent-Monoid

  is-set-type-Idempotent-Monoid : is-set type-Idempotent-Monoid
  is-set-type-Idempotent-Monoid = is-set-type-Band band-Idempotent-Monoid

  unit-Idempotent-Monoid : type-Idempotent-Monoid
  unit-Idempotent-Monoid = unit-Monoid monoid-Idempotent-Monoid

  mul-Idempotent-Monoid :
    type-Idempotent-Monoid → type-Idempotent-Monoid → type-Idempotent-Monoid
  mul-Idempotent-Monoid = mul-Band band-Idempotent-Monoid

  mul-Idempotent-Monoid' :
    type-Idempotent-Monoid → type-Idempotent-Monoid → type-Idempotent-Monoid
  mul-Idempotent-Monoid' = mul-Band' band-Idempotent-Monoid

  ap-mul-Idempotent-Monoid :
    {x x' y y' : type-Idempotent-Monoid} →
    x ＝ x' → y ＝ y' → mul-Idempotent-Monoid x y ＝ mul-Idempotent-Monoid x' y'
  ap-mul-Idempotent-Monoid = ap-mul-Band band-Idempotent-Monoid

  associative-mul-Idempotent-Monoid :
    (x y z : type-Idempotent-Monoid) →
    mul-Idempotent-Monoid (mul-Idempotent-Monoid x y) z ＝
    mul-Idempotent-Monoid x (mul-Idempotent-Monoid y z)
  associative-mul-Idempotent-Monoid =
    associative-mul-Band band-Idempotent-Monoid

  left-unit-law-mul-Idempotent-Monoid :
    (x : type-Idempotent-Monoid) →
    mul-Idempotent-Monoid unit-Idempotent-Monoid x ＝ x
  left-unit-law-mul-Idempotent-Monoid =
    left-unit-law-mul-Monoid monoid-Idempotent-Monoid

  right-unit-law-mul-Idempotent-Monoid :
    (x : type-Idempotent-Monoid) →
    mul-Idempotent-Monoid x unit-Idempotent-Monoid ＝ x
  right-unit-law-mul-Idempotent-Monoid =
    right-unit-law-mul-Monoid monoid-Idempotent-Monoid  

  left-swap-mul-Idempotent-Monoid :
    {x y z : type-Idempotent-Monoid} →
    mul-Idempotent-Monoid x y ＝ mul-Idempotent-Monoid y x →
    mul-Idempotent-Monoid x (mul-Idempotent-Monoid y z) ＝
    mul-Idempotent-Monoid y (mul-Idempotent-Monoid x z)
  left-swap-mul-Idempotent-Monoid =
    left-swap-mul-Band band-Idempotent-Monoid

  right-swap-mul-Idempotent-Monoid :
    {x y z : type-Idempotent-Monoid} →
    mul-Idempotent-Monoid y z ＝ mul-Idempotent-Monoid z y →
    mul-Idempotent-Monoid (mul-Idempotent-Monoid x y) z ＝
    mul-Idempotent-Monoid (mul-Idempotent-Monoid x z) y
  right-swap-mul-Idempotent-Monoid =
    right-swap-mul-Band band-Idempotent-Monoid

  interchange-mul-mul-Idempotent-Monoid :
    {x y z w : type-Idempotent-Monoid} →
    mul-Idempotent-Monoid y z ＝ mul-Idempotent-Monoid z y →
    mul-Idempotent-Monoid
      ( mul-Idempotent-Monoid x y)
      ( mul-Idempotent-Monoid z w) ＝
    mul-Idempotent-Monoid
      ( mul-Idempotent-Monoid x z)
      ( mul-Idempotent-Monoid y w)
  interchange-mul-mul-Idempotent-Monoid =
    interchange-mul-mul-Band band-Idempotent-Monoid

  magma-Idempotent-Monoid : Magma l1
  magma-Idempotent-Monoid = magma-Band band-Idempotent-Monoid
```
