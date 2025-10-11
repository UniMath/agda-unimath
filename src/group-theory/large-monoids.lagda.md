# Large monoids

```agda
module group-theory.large-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.large-similarity-relations
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.large-semigroups
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

A {{#concept "large monoid" Agda=Large-Monoid}} is a
[large semigroup](group-theory.large-semigroups.md) with an
[identity element](foundation.unital-binary-operations.md), further endowed with
a [large similarity relation](foundation.large-similarity-relations.md)
preserved by the binary operation of the monoid, and an operation to
[raise the universe level](foundation.raising-universe-levels.md) of an element.

## Definition

```agda
record Large-Monoid (α : Level → Level) (β : Level → Level → Level) : UUω where
  constructor
    make-Large-Monoid
  field
    large-semigroup-Large-Monoid : Large-Semigroup α

  type-Large-Monoid : (l : Level) → UU (α l)
  type-Large-Monoid = type-Large-Semigroup large-semigroup-Large-Monoid

  field
    large-similarity-relation-Large-Monoid :
      Large-Similarity-Relation β type-Large-Monoid

  sim-prop-Large-Monoid : Large-Relation-Prop β type-Large-Monoid
  sim-prop-Large-Monoid =
    sim-prop-Large-Similarity-Relation large-similarity-relation-Large-Monoid

  sim-Large-Monoid : Large-Relation β type-Large-Monoid
  sim-Large-Monoid x y = type-Prop (sim-prop-Large-Monoid x y)

  refl-sim-Large-Monoid :
    is-reflexive-Large-Relation-Prop type-Large-Monoid sim-prop-Large-Monoid
  refl-sim-Large-Monoid =
    refl-sim-Large-Similarity-Relation large-similarity-relation-Large-Monoid

  sim-eq-Large-Monoid :
    {l : Level} {x y : type-Large-Monoid l} → x ＝ y → sim-Large-Monoid x y
  sim-eq-Large-Monoid =
    sim-eq-Large-Similarity-Relation large-similarity-relation-Large-Monoid

  symmetric-sim-Large-Monoid :
    is-symmetric-Large-Relation-Prop type-Large-Monoid sim-prop-Large-Monoid
  symmetric-sim-Large-Monoid =
    symmetric-sim-Large-Similarity-Relation
      ( large-similarity-relation-Large-Monoid)

  transitive-sim-Large-Monoid :
    is-transitive-Large-Relation-Prop type-Large-Monoid sim-prop-Large-Monoid
  transitive-sim-Large-Monoid =
    transitive-sim-Large-Similarity-Relation
      ( large-similarity-relation-Large-Monoid)

  eq-sim-Large-Monoid :
    {l : Level} (x y : type-Large-Monoid l) → sim-Large-Monoid x y → x ＝ y
  eq-sim-Large-Monoid =
    eq-sim-Large-Similarity-Relation large-similarity-relation-Large-Monoid

  field
    raise-Large-Monoid :
      {l1 : Level} (l2 : Level) → type-Large-Monoid l1 →
      type-Large-Monoid (l1 ⊔ l2)
    sim-raise-Large-Monoid :
      {l1 : Level} (l2 : Level) (x : type-Large-Monoid l1) →
      sim-Large-Monoid x (raise-Large-Monoid l2 x)

  mul-Large-Monoid :
    {l1 l2 : Level} → type-Large-Monoid l1 → type-Large-Monoid l2 →
    type-Large-Monoid (l1 ⊔ l2)
  mul-Large-Monoid =
    mul-Large-Semigroup large-semigroup-Large-Monoid

  ap-mul-Large-Monoid :
    {l1 l2 : Level} →
    {x x' : type-Large-Monoid l1} → x ＝ x' →
    {y y' : type-Large-Monoid l2} → y ＝ y' →
    mul-Large-Monoid x y ＝ mul-Large-Monoid x' y'
  ap-mul-Large-Monoid = ap-binary mul-Large-Monoid

  field
    preserves-sim-mul-Large-Monoid :
      {l1 l2 l3 l4 : Level}
      (x : type-Large-Monoid l1) (x' : type-Large-Monoid l2) →
      sim-Large-Monoid x x' →
      (y : type-Large-Monoid l3) (y' : type-Large-Monoid l4) →
      sim-Large-Monoid y y' →
      sim-Large-Monoid (mul-Large-Monoid x y) (mul-Large-Monoid x' y')

  field
    unit-Large-Monoid : type-Large-Monoid lzero
    left-unit-law-Large-Monoid :
      {l : Level} (x : type-Large-Monoid l) →
      mul-Large-Monoid unit-Large-Monoid x ＝ x
    right-unit-law-Large-Monoid :
      {l : Level} (x : type-Large-Monoid l) →
      mul-Large-Monoid x unit-Large-Monoid ＝ x

  raise-unit-Large-Monoid : (l : Level) → type-Large-Monoid l
  raise-unit-Large-Monoid l = raise-Large-Monoid l unit-Large-Monoid

  abstract
    raise-unit-lzero-Large-Monoid :
      raise-unit-Large-Monoid lzero ＝ unit-Large-Monoid
    raise-unit-lzero-Large-Monoid =
      eq-sim-Large-Monoid _ _
        ( symmetric-sim-Large-Monoid _ _ (sim-raise-Large-Monoid _ _))

  associative-mul-Large-Monoid :
    {l1 l2 l3 : Level} →
    (x : type-Large-Monoid l1) (y : type-Large-Monoid l2)
    (z : type-Large-Monoid l3) →
    mul-Large-Monoid (mul-Large-Monoid x y) z ＝
    mul-Large-Monoid x (mul-Large-Monoid y z)
  associative-mul-Large-Monoid =
    associative-mul-Large-Semigroup large-semigroup-Large-Monoid

  semigroup-Large-Monoid : (l : Level) → Semigroup (α l)
  semigroup-Large-Monoid =
    semigroup-Large-Semigroup large-semigroup-Large-Monoid

open Large-Monoid public
```

## Properties

### Similarity reasoning in large monoids

```agda
module
  similarity-reasoning-Large-Monoid
    {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  open similarity-reasoning-Large-Similarity-Relation
    ( large-similarity-relation-Large-Monoid M) public
```

### Multiplication preserves similarity on each side

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  abstract
    preserves-sim-left-mul-Large-Monoid :
      {l1 l2 l3 : Level} (y : type-Large-Monoid M l1) →
      (x : type-Large-Monoid M l2) (x' : type-Large-Monoid M l3) →
      sim-Large-Monoid M x x' →
      sim-Large-Monoid M (mul-Large-Monoid M x y) (mul-Large-Monoid M x' y)
    preserves-sim-left-mul-Large-Monoid y x x' x~x' =
      preserves-sim-mul-Large-Monoid M x x' x~x' y y (refl-sim-Large-Monoid M y)

    preserves-sim-right-mul-Large-Monoid :
      {l1 l2 l3 : Level} (x : type-Large-Monoid M l1) →
      (y : type-Large-Monoid M l2) (y' : type-Large-Monoid M l3) →
      sim-Large-Monoid M y y' →
      sim-Large-Monoid M (mul-Large-Monoid M x y) (mul-Large-Monoid M x y')
    preserves-sim-right-mul-Large-Monoid x =
      preserves-sim-mul-Large-Monoid M x x (refl-sim-Large-Monoid M x)
```

### Raised unit laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  abstract
    raise-left-unit-law-Large-Monoid :
      {l1 l2 : Level} (x : type-Large-Monoid M l1) →
      sim-Large-Monoid M (mul-Large-Monoid M (raise-unit-Large-Monoid M l2) x) x
    raise-left-unit-law-Large-Monoid x =
      transitive-sim-Large-Monoid M
        ( mul-Large-Monoid M (raise-unit-Large-Monoid M _) x)
        ( mul-Large-Monoid M (unit-Large-Monoid M) x)
        ( x)
        ( sim-eq-Large-Monoid M (left-unit-law-Large-Monoid M x))
        ( preserves-sim-left-mul-Large-Monoid M x _ _
          ( symmetric-sim-Large-Monoid M _ _
            ( sim-raise-Large-Monoid M _ (unit-Large-Monoid M))))

    raise-right-unit-law-Large-Monoid :
      {l1 l2 : Level} (x : type-Large-Monoid M l1) →
      sim-Large-Monoid M (mul-Large-Monoid M x (raise-unit-Large-Monoid M l2)) x
    raise-right-unit-law-Large-Monoid x =
      transitive-sim-Large-Monoid M
        ( mul-Large-Monoid M x (raise-unit-Large-Monoid M _))
        ( mul-Large-Monoid M x (unit-Large-Monoid M))
        ( x)
        ( sim-eq-Large-Monoid M (right-unit-law-Large-Monoid M x))
        ( preserves-sim-right-mul-Large-Monoid M x _ _
          ( symmetric-sim-Large-Monoid M _ _
            ( sim-raise-Large-Monoid M _ (unit-Large-Monoid M))))
```

### Small monoids from large monoids

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  monoid-Large-Monoid : (l : Level) → Monoid (α l)
  monoid-Large-Monoid l =
    ( semigroup-Large-Monoid M l ,
      raise-unit-Large-Monoid M l ,
      ( λ x →
        eq-sim-Large-Monoid M _ _ (raise-left-unit-law-Large-Monoid M x)) ,
      ( λ x →
        eq-sim-Large-Monoid M _ _ (raise-right-unit-law-Large-Monoid M x)))
```
