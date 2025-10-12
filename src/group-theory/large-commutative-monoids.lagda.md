# Large commutative monoids

```agda
module group-theory.large-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.large-similarity-relations
open import foundation.logical-equivalences
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.homomorphisms-commutative-monoids
open import group-theory.large-monoids
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

A {{#concept "large commutative monoid" Agda=Large-Commutative-Monoid}} is a
[large monoid](group-theory.large-monoids.md) whose binary operation is
commutative.

## Definition

```agda
record
  Large-Commutative-Monoid (α : Level → Level) (β : Level → Level → Level) : UUω
  where

  constructor
    make-Large-Commutative-Monoid

  field
    large-monoid-Large-Commutative-Monoid : Large-Monoid α β

  type-Large-Commutative-Monoid : (l : Level) → UU (α l)
  type-Large-Commutative-Monoid =
    type-Large-Monoid large-monoid-Large-Commutative-Monoid

  set-Large-Commutative-Monoid : (l : Level) → Set (α l)
  set-Large-Commutative-Monoid =
    set-Large-Monoid large-monoid-Large-Commutative-Monoid

  mul-Large-Commutative-Monoid :
    {l1 l2 : Level} →
    type-Large-Commutative-Monoid l1 → type-Large-Commutative-Monoid l2 →
    type-Large-Commutative-Monoid (l1 ⊔ l2)
  mul-Large-Commutative-Monoid =
    mul-Large-Monoid large-monoid-Large-Commutative-Monoid

  unit-Large-Commutative-Monoid : type-Large-Commutative-Monoid lzero
  unit-Large-Commutative-Monoid =
    unit-Large-Monoid large-monoid-Large-Commutative-Monoid

  field
    commutative-mul-Large-Commutative-Monoid :
      {l1 l2 : Level} →
      (x : type-Large-Commutative-Monoid l1) →
      (y : type-Large-Commutative-Monoid l2) →
      mul-Large-Commutative-Monoid x y ＝ mul-Large-Commutative-Monoid y x

open Large-Commutative-Monoid public
```

## Properties

### The similarity relation of a large commutative monoid

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  where

  sim-prop-Large-Commutative-Monoid :
    Large-Relation-Prop β (type-Large-Commutative-Monoid M)
  sim-prop-Large-Commutative-Monoid =
    sim-prop-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  sim-Large-Commutative-Monoid :
    Large-Relation β (type-Large-Commutative-Monoid M)
  sim-Large-Commutative-Monoid =
    sim-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  refl-sim-Large-Commutative-Monoid :
    {l : Level} (x : type-Large-Commutative-Monoid M l) →
    sim-Large-Commutative-Monoid x x
  refl-sim-Large-Commutative-Monoid =
    refl-sim-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  symmetric-sim-Large-Commutative-Monoid :
    {l1 l2 : Level} →
    (x : type-Large-Commutative-Monoid M l1) →
    (y : type-Large-Commutative-Monoid M l2) →
    sim-Large-Commutative-Monoid x y → sim-Large-Commutative-Monoid y x
  symmetric-sim-Large-Commutative-Monoid =
    symmetric-sim-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  transitive-sim-Large-Commutative-Monoid :
    {l1 l2 l3 : Level} →
    (x : type-Large-Commutative-Monoid M l1) →
    (y : type-Large-Commutative-Monoid M l2) →
    (z : type-Large-Commutative-Monoid M l3) →
    sim-Large-Commutative-Monoid y z → sim-Large-Commutative-Monoid x y →
    sim-Large-Commutative-Monoid x z
  transitive-sim-Large-Commutative-Monoid =
    transitive-sim-Large-Monoid (large-monoid-Large-Commutative-Monoid M)
```

### Raising universe levels

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  where

  raise-Large-Commutative-Monoid :
    {l1 : Level} (l2 : Level) (x : type-Large-Commutative-Monoid M l1) →
    type-Large-Commutative-Monoid M (l1 ⊔ l2)
  raise-Large-Commutative-Monoid =
    raise-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  raise-unit-Large-Commutative-Monoid :
    (l : Level) → type-Large-Commutative-Monoid M l
  raise-unit-Large-Commutative-Monoid =
    raise-unit-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  sim-raise-Large-Commutative-Monoid :
    {l1 : Level} (l2 : Level) (x : type-Large-Commutative-Monoid M l1) →
    sim-Large-Commutative-Monoid M x (raise-Large-Commutative-Monoid l2 x)
  sim-raise-Large-Commutative-Monoid =
    sim-raise-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  sim-raise-Large-Commutative-Monoid' :
    {l1 : Level} (l2 : Level) (x : type-Large-Commutative-Monoid M l1) →
    sim-Large-Commutative-Monoid M (raise-Large-Commutative-Monoid l2 x) x
  sim-raise-Large-Commutative-Monoid' =
    sim-raise-Large-Monoid' (large-monoid-Large-Commutative-Monoid M)

  raise-raise-Large-Commutative-Monoid :
    {l1 l2 l3 : Level} → (x : type-Large-Commutative-Monoid M l1) →
    raise-Large-Commutative-Monoid l2 (raise-Large-Commutative-Monoid l3 x) ＝
    raise-Large-Commutative-Monoid (l2 ⊔ l3) x
  raise-raise-Large-Commutative-Monoid =
    raise-raise-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  raise-left-mul-Large-Commutative-Monoid :
    {l1 l2 l3 : Level} →
    (x : type-Large-Commutative-Monoid M l1) →
    (y : type-Large-Commutative-Monoid M l2) →
    mul-Large-Commutative-Monoid M (raise-Large-Commutative-Monoid l3 x) y ＝
    raise-Large-Commutative-Monoid l3 (mul-Large-Commutative-Monoid M x y)
  raise-left-mul-Large-Commutative-Monoid =
    raise-left-mul-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  raise-right-mul-Large-Commutative-Monoid :
    {l1 l2 l3 : Level} →
    (x : type-Large-Commutative-Monoid M l1) →
    (y : type-Large-Commutative-Monoid M l2) →
    mul-Large-Commutative-Monoid M x (raise-Large-Commutative-Monoid l3 y) ＝
    raise-Large-Commutative-Monoid l3 (mul-Large-Commutative-Monoid M x y)
  raise-right-mul-Large-Commutative-Monoid =
    raise-right-mul-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  raise-left-unit-law-Large-Commutative-Monoid :
    {l1 l2 : Level} (x : type-Large-Commutative-Monoid M l1) →
    mul-Large-Commutative-Monoid M (raise-unit-Large-Commutative-Monoid l2) x ＝
    raise-Large-Commutative-Monoid l2 x
  raise-left-unit-law-Large-Commutative-Monoid =
    raise-left-unit-law-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  raise-right-unit-law-Large-Commutative-Monoid :
    {l1 l2 : Level} (x : type-Large-Commutative-Monoid M l1) →
    mul-Large-Commutative-Monoid M x (raise-unit-Large-Commutative-Monoid l2) ＝
    raise-Large-Commutative-Monoid l2 x
  raise-right-unit-law-Large-Commutative-Monoid =
    raise-right-unit-law-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  raise-unit-lzero-Large-Commutative-Monoid :
    raise-unit-Large-Commutative-Monoid lzero ＝ unit-Large-Commutative-Monoid M
  raise-unit-lzero-Large-Commutative-Monoid =
    raise-unit-lzero-Large-Monoid (large-monoid-Large-Commutative-Monoid M)
```

### Monoid properties of large commutative monoids

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  where

  associative-mul-Large-Commutative-Monoid :
    {l1 l2 l3 : Level} →
    (x : type-Large-Commutative-Monoid M l1) →
    (y : type-Large-Commutative-Monoid M l2) →
    (z : type-Large-Commutative-Monoid M l3) →
    mul-Large-Commutative-Monoid M (mul-Large-Commutative-Monoid M x y) z ＝
    mul-Large-Commutative-Monoid M x (mul-Large-Commutative-Monoid M y z)
  associative-mul-Large-Commutative-Monoid =
    associative-mul-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  left-unit-law-mul-Large-Commutative-Monoid :
    {l : Level} → (x : type-Large-Commutative-Monoid M l) →
    mul-Large-Commutative-Monoid M (unit-Large-Commutative-Monoid M) x ＝ x
  left-unit-law-mul-Large-Commutative-Monoid =
    left-unit-law-mul-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  right-unit-law-mul-Large-Commutative-Monoid :
    {l : Level} → (x : type-Large-Commutative-Monoid M l) →
    mul-Large-Commutative-Monoid M x (unit-Large-Commutative-Monoid M) ＝ x
  right-unit-law-mul-Large-Commutative-Monoid =
    right-unit-law-mul-Large-Monoid (large-monoid-Large-Commutative-Monoid M)
```
