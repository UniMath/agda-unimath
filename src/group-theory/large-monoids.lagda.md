# Large monoids

```agda
module group-theory.large-monoids where
```

<details><summary>Imports</summary>

```agda
open import group-theory.monoids
open import group-theory.large-semigroups
open import foundation.universe-levels
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.identity-types
open import foundation.large-similarity-relations
open import foundation.dependent-pair-types
```

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

  field
    preserves-sim-mul-Large-Monoid :
      {l1 l2 l3 l4 : Level}
      (x : type-Large-Monoid l1) (x' : type-Large-Monoid l2) →
      sim-Large-Monoid x x' →
      (y : type-Large-Monoid l3) (y' : type-Large-Monoid l4) →
      sim-Large-Monoid y y' →
      sim-Large-Monoid (mul-Large-Monoid x y) (mul-Large-Monoid x' y')

  preserves-sim-left-mul-Large-Monoid :
    {l1 l2 l3 : Level} (y : type-Large-Monoid l1) →
    (x : type-Large-Monoid l2) (x' : type-Large-Monoid l3) →
    sim-Large-Monoid x x' →
    sim-Large-Monoid (mul-Large-Monoid x y) (mul-Large-Monoid x' y)
  preserves-sim-left-mul-Large-Monoid y x x' x~x' =
    preserves-sim-mul-Large-Monoid x x' x~x' y y (refl-sim-Large-Monoid y)

  preserves-sim-right-mul-Large-Monoid :
    {l1 l2 l3 : Level} (x : type-Large-Monoid l1) →
    (y : type-Large-Monoid l2) (y' : type-Large-Monoid l3) →
    sim-Large-Monoid y y' →
    sim-Large-Monoid (mul-Large-Monoid x y) (mul-Large-Monoid x y')
  preserves-sim-right-mul-Large-Monoid x =
    preserves-sim-mul-Large-Monoid x x (refl-sim-Large-Monoid x)

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

  raise-left-unit-law-Large-Monoid :
    {l : Level} (x : type-Large-Monoid l) →
    mul-Large-Monoid (raise-unit-Large-Monoid l) x ＝ x
  raise-left-unit-law-Large-Monoid x =
    eq-sim-Large-Monoid _ _
      {!   !}

  associative-mul-Large-Monoid :
    {l1 l2 l3 : Level} →
    (x : type-Large-Monoid l1) (y : type-Large-Monoid l2)
    (z : type-Large-Monoid l3) →
    mul-Large-Monoid (mul-Large-Monoid x y) z ＝
    mul-Large-Monoid x (mul-Large-Monoid y z)
  associative-mul-Large-Monoid =
    associative-mul-Large-Semigroup large-semigroup-Large-Monoid
```
