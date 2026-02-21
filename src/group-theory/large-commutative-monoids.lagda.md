# Large commutative monoids

```agda
module group-theory.large-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cumulative-large-sets
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.large-similarity-relations
open import foundation.logical-equivalences
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.sets
open import foundation.similarity-preserving-binary-maps-cumulative-large-sets
open import foundation.similarity-preserving-maps-cumulative-large-sets
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

  cumulative-large-set-Large-Commutative-Monoid : Cumulative-Large-Set α β
  cumulative-large-set-Large-Commutative-Monoid =
    cumulative-large-set-Large-Monoid large-monoid-Large-Commutative-Monoid

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

  mul-Large-Commutative-Monoid' :
    {l1 l2 : Level} →
    type-Large-Commutative-Monoid l1 → type-Large-Commutative-Monoid l2 →
    type-Large-Commutative-Monoid (l1 ⊔ l2)
  mul-Large-Commutative-Monoid' x y = mul-Large-Commutative-Monoid y x

  ap-mul-Large-Commutative-Monoid :
    {l1 l2 : Level} →
    {x x' : type-Large-Commutative-Monoid l1} → x ＝ x' →
    {y y' : type-Large-Commutative-Monoid l2} → y ＝ y' →
    mul-Large-Commutative-Monoid x y ＝ mul-Large-Commutative-Monoid x' y'
  ap-mul-Large-Commutative-Monoid =
    ap-mul-Large-Monoid large-monoid-Large-Commutative-Monoid

  field
    commutative-mul-Large-Commutative-Monoid :
      {l1 l2 : Level} →
      (x : type-Large-Commutative-Monoid l1) →
      (y : type-Large-Commutative-Monoid l2) →
      mul-Large-Commutative-Monoid x y ＝ mul-Large-Commutative-Monoid y x

open Large-Commutative-Monoid public
```

## Properties

### Similarity

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  where

  large-similarity-relation-Large-Commutative-Monoid :
    Large-Similarity-Relation β (type-Large-Commutative-Monoid M)
  large-similarity-relation-Large-Commutative-Monoid =
    large-similarity-relation-Large-Monoid
      ( large-monoid-Large-Commutative-Monoid M)

  sim-prop-Large-Commutative-Monoid :
    Large-Relation-Prop β (type-Large-Commutative-Monoid M)
  sim-prop-Large-Commutative-Monoid =
    sim-prop-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  sim-Large-Commutative-Monoid :
    Large-Relation β (type-Large-Commutative-Monoid M)
  sim-Large-Commutative-Monoid =
    sim-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  refl-sim-Large-Commutative-Monoid :
    is-reflexive-Large-Relation
      ( type-Large-Commutative-Monoid M)
      ( sim-Large-Commutative-Monoid)
  refl-sim-Large-Commutative-Monoid =
    refl-sim-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  symmetric-sim-Large-Commutative-Monoid :
    is-symmetric-Large-Relation
      ( type-Large-Commutative-Monoid M)
      ( sim-Large-Commutative-Monoid)
  symmetric-sim-Large-Commutative-Monoid =
    symmetric-sim-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  transitive-sim-Large-Commutative-Monoid :
    is-transitive-Large-Relation
      ( type-Large-Commutative-Monoid M)
      ( sim-Large-Commutative-Monoid)
  transitive-sim-Large-Commutative-Monoid =
    transitive-sim-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  sim-eq-Large-Commutative-Monoid :
    {l : Level} {x y : type-Large-Commutative-Monoid M l} →
    x ＝ y → sim-Large-Commutative-Monoid x y
  sim-eq-Large-Commutative-Monoid =
    sim-eq-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  eq-sim-Large-Commutative-Monoid :
    {l : Level} (x y : type-Large-Commutative-Monoid M l) →
    sim-Large-Commutative-Monoid x y → x ＝ y
  eq-sim-Large-Commutative-Monoid =
    eq-sim-Large-Monoid (large-monoid-Large-Commutative-Monoid M)
```

### Raising universe levels

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  where

  raise-Large-Commutative-Monoid :
    {l0 : Level} (l : Level) →
    type-Large-Commutative-Monoid M l0 →
    type-Large-Commutative-Monoid M (l0 ⊔ l)
  raise-Large-Commutative-Monoid =
    raise-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  sim-raise-Large-Commutative-Monoid :
    {l0 : Level} (l : Level) (x : type-Large-Commutative-Monoid M l0) →
    sim-Large-Commutative-Monoid M x (raise-Large-Commutative-Monoid l x)
  sim-raise-Large-Commutative-Monoid =
    sim-raise-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  sim-raise-Large-Commutative-Monoid' :
    {l0 : Level} (l : Level) (x : type-Large-Commutative-Monoid M l0) →
    sim-Large-Commutative-Monoid M (raise-Large-Commutative-Monoid l x) x
  sim-raise-Large-Commutative-Monoid' =
    sim-raise-Large-Monoid' (large-monoid-Large-Commutative-Monoid M)

  eq-raise-Large-Commutative-Monoid :
    {l : Level} (x : type-Large-Commutative-Monoid M l) →
    raise-Large-Commutative-Monoid l x ＝ x
  eq-raise-Large-Commutative-Monoid =
    eq-raise-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  is-emb-raise-Large-Commutative-Monoid :
    (l1 l2 : Level) → is-emb (raise-Large-Commutative-Monoid {l1} l2)
  is-emb-raise-Large-Commutative-Monoid =
    is-emb-raise-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  emb-raise-Large-Commutative-Monoid :
    (l1 l2 : Level) →
    type-Large-Commutative-Monoid M l1 ↪
    type-Large-Commutative-Monoid M (l1 ⊔ l2)
  emb-raise-Large-Commutative-Monoid =
    emb-raise-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  raise-raise-Large-Commutative-Monoid :
    {l0 : Level} (l1 l2 : Level) (x : type-Large-Commutative-Monoid M l0) →
    raise-Large-Commutative-Monoid l1 (raise-Large-Commutative-Monoid l2 x) ＝
    raise-Large-Commutative-Monoid (l1 ⊔ l2) x
  raise-raise-Large-Commutative-Monoid =
    raise-raise-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  eq-raise-sim-Large-Commutative-Monoid :
    {l1 l2 : Level}
    (x : type-Large-Commutative-Monoid M l1)
    (y : type-Large-Commutative-Monoid M l2) →
    sim-Large-Commutative-Monoid M x y →
    raise-Large-Commutative-Monoid l2 x ＝ raise-Large-Commutative-Monoid l1 y
  eq-raise-sim-Large-Commutative-Monoid =
    eq-raise-sim-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  sim-eq-raise-Large-Commutative-Monoid :
    {l1 l2 : Level}
    (x : type-Large-Commutative-Monoid M l1)
    (y : type-Large-Commutative-Monoid M l2) →
    raise-Large-Commutative-Monoid l2 x ＝ raise-Large-Commutative-Monoid l1 y →
    sim-Large-Commutative-Monoid M x y
  sim-eq-raise-Large-Commutative-Monoid =
    sim-eq-raise-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  eq-raise-iff-sim-Large-Commutative-Monoid :
    {l1 l2 : Level} →
    (x : type-Large-Commutative-Monoid M l1)
    (y : type-Large-Commutative-Monoid M l2) →
    ( sim-Large-Commutative-Monoid M x y ↔
      ( raise-Large-Commutative-Monoid l2 x ＝
        raise-Large-Commutative-Monoid l1 y))
  eq-raise-iff-sim-Large-Commutative-Monoid =
    eq-raise-iff-sim-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  eq-raise-sim-Large-Commutative-Monoid' :
    {l1 l2 : Level}
    (x : type-Large-Commutative-Monoid M (l1 ⊔ l2))
    (y : type-Large-Commutative-Monoid M l2) →
    sim-Large-Commutative-Monoid M x y →
    x ＝ raise-Large-Commutative-Monoid l1 y
  eq-raise-sim-Large-Commutative-Monoid' =
    eq-raise-sim-Large-Monoid' (large-monoid-Large-Commutative-Monoid M)
```

### Similarity preservation of multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  where

  sim-preserving-binary-operator-mul-Large-Commutative-Monoid :
    sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Commutative-Monoid M)
  sim-preserving-binary-operator-mul-Large-Commutative-Monoid =
    sim-preserving-binary-operator-mul-Large-Monoid
      ( large-monoid-Large-Commutative-Monoid M)

  preserves-sim-mul-Large-Commutative-Monoid :
    preserves-sim-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Commutative-Monoid M)
      ( mul-Large-Commutative-Monoid M)
  preserves-sim-mul-Large-Commutative-Monoid =
    preserves-sim-mul-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  sim-preserving-map-left-mul-Large-Commutative-Monoid :
    {l : Level} (x : type-Large-Commutative-Monoid M l) →
    sim-preserving-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Commutative-Monoid M)
  sim-preserving-map-left-mul-Large-Commutative-Monoid =
    sim-preserving-map-left-mul-Large-Monoid
      ( large-monoid-Large-Commutative-Monoid M)

  preserves-sim-left-mul-Large-Commutative-Monoid :
    {l : Level} (x : type-Large-Commutative-Monoid M l) →
    preserves-sim-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Commutative-Monoid M)
      ( mul-Large-Commutative-Monoid M x)
  preserves-sim-left-mul-Large-Commutative-Monoid =
    preserves-sim-left-mul-Large-Monoid
      ( large-monoid-Large-Commutative-Monoid M)

  sim-preserving-map-right-mul-Large-Commutative-Monoid :
    {l : Level} (y : type-Large-Commutative-Monoid M l) →
    sim-preserving-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Commutative-Monoid M)
  sim-preserving-map-right-mul-Large-Commutative-Monoid =
    sim-preserving-map-right-mul-Large-Monoid
      ( large-monoid-Large-Commutative-Monoid M)

  preserves-sim-right-mul-Large-Commutative-Monoid :
    {l : Level} (y : type-Large-Commutative-Monoid M l) →
    preserves-sim-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Commutative-Monoid M)
      ( mul-Large-Commutative-Monoid' M y)
  preserves-sim-right-mul-Large-Commutative-Monoid =
    preserves-sim-right-mul-Large-Monoid
      ( large-monoid-Large-Commutative-Monoid M)
```

### Raising universe levels in multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  where

  abstract
    mul-raise-right-Large-Commutative-Monoid :
      {l1 l2 : Level} (l3 : Level)
      (x : type-Large-Commutative-Monoid M l1)
      (y : type-Large-Commutative-Monoid M l2) →
      mul-Large-Commutative-Monoid M
        ( x)
        ( raise-Large-Commutative-Monoid M l3 y) ＝
      raise-Large-Commutative-Monoid M l3 (mul-Large-Commutative-Monoid M x y)
    mul-raise-right-Large-Commutative-Monoid =
      mul-raise-right-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

    mul-raise-left-Large-Commutative-Monoid :
      {l1 l2 : Level} (l3 : Level)
      (x : type-Large-Commutative-Monoid M l1)
      (y : type-Large-Commutative-Monoid M l2) →
      mul-Large-Commutative-Monoid M
        ( raise-Large-Commutative-Monoid M l3 x)
        ( y) ＝
      raise-Large-Commutative-Monoid M l3 (mul-Large-Commutative-Monoid M x y)
    mul-raise-left-Large-Commutative-Monoid =
      mul-raise-left-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

    mul-raise-raise-Large-Commutative-Monoid :
      {l1 l2 : Level} (l3 l4 : Level)
      (x : type-Large-Commutative-Monoid M l1)
      (y : type-Large-Commutative-Monoid M l2) →
      mul-Large-Commutative-Monoid M
        ( raise-Large-Commutative-Monoid M l3 x)
        ( raise-Large-Commutative-Monoid M l4 y) ＝
      raise-Large-Commutative-Monoid M
        ( l3 ⊔ l4)
        ( mul-Large-Commutative-Monoid M x y)
    mul-raise-raise-Large-Commutative-Monoid =
      mul-raise-raise-Large-Monoid (large-monoid-Large-Commutative-Monoid M)
```

### Semigroup laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  where

  associative-mul-Large-Commutative-Monoid :
    {l1 l2 l3 : Level}
    (x : type-Large-Commutative-Monoid M l1)
    (y : type-Large-Commutative-Monoid M l2)
    (z : type-Large-Commutative-Monoid M l3) →
    mul-Large-Commutative-Monoid M (mul-Large-Commutative-Monoid M x y) z ＝
    mul-Large-Commutative-Monoid M x (mul-Large-Commutative-Monoid M y z)
  associative-mul-Large-Commutative-Monoid =
    associative-mul-Large-Monoid (large-monoid-Large-Commutative-Monoid M)
```

### Monoid laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  where

  unit-Large-Commutative-Monoid : type-Large-Commutative-Monoid M lzero
  unit-Large-Commutative-Monoid =
    unit-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  raise-unit-Large-Commutative-Monoid :
    (l : Level) → type-Large-Commutative-Monoid M l
  raise-unit-Large-Commutative-Monoid =
    raise-unit-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  is-unit-prop-Large-Commutative-Monoid :
    {l : Level} → type-Large-Commutative-Monoid M l → Prop (β l lzero)
  is-unit-prop-Large-Commutative-Monoid =
    is-unit-prop-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  is-unit-Large-Commutative-Monoid :
    {l : Level} → type-Large-Commutative-Monoid M l → UU (β l lzero)
  is-unit-Large-Commutative-Monoid =
    is-unit-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  is-unit-unit-Large-Commutative-Monoid :
    is-unit-Large-Commutative-Monoid unit-Large-Commutative-Monoid
  is-unit-unit-Large-Commutative-Monoid =
    is-unit-unit-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  is-unit-raise-unit-Large-Commutative-Monoid :
    (l : Level) →
    is-unit-Large-Commutative-Monoid (raise-unit-Large-Commutative-Monoid l)
  is-unit-raise-unit-Large-Commutative-Monoid =
    is-unit-raise-unit-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  eq-raise-unit-is-unit-Large-Commutative-Monoid :
    {l : Level} (x : type-Large-Commutative-Monoid M l) →
    is-unit-Large-Commutative-Monoid x →
    x ＝ raise-unit-Large-Commutative-Monoid l
  eq-raise-unit-is-unit-Large-Commutative-Monoid =
    eq-raise-unit-is-unit-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  left-unit-law-mul-Large-Commutative-Monoid :
    {l : Level} (x : type-Large-Commutative-Monoid M l) →
    mul-Large-Commutative-Monoid M unit-Large-Commutative-Monoid x ＝ x
  left-unit-law-mul-Large-Commutative-Monoid =
    left-unit-law-mul-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  right-unit-law-mul-Large-Commutative-Monoid :
    {l : Level} (x : type-Large-Commutative-Monoid M l) →
    mul-Large-Commutative-Monoid M x unit-Large-Commutative-Monoid ＝ x
  right-unit-law-mul-Large-Commutative-Monoid =
    right-unit-law-mul-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  left-raise-unit-law-mul-Large-Commutative-Monoid :
    {l1 l2 : Level} (y : type-Large-Commutative-Monoid M l2) →
    mul-Large-Commutative-Monoid M (raise-unit-Large-Commutative-Monoid l1) y ＝
    raise-Large-Commutative-Monoid M l1 y
  left-raise-unit-law-mul-Large-Commutative-Monoid =
    left-raise-unit-law-mul-Large-Monoid
      ( large-monoid-Large-Commutative-Monoid M)

  right-raise-unit-law-mul-Large-Commutative-Monoid :
    {l1 l2 : Level} (x : type-Large-Commutative-Monoid M l1) →
    mul-Large-Commutative-Monoid M x (raise-unit-Large-Commutative-Monoid l2) ＝
    raise-Large-Commutative-Monoid M l2 x
  right-raise-unit-law-mul-Large-Commutative-Monoid =
    right-raise-unit-law-mul-Large-Monoid
      ( large-monoid-Large-Commutative-Monoid M)

  eq-left-is-unit-law-mul-Large-Commutative-Monoid :
    {l1 l2 : Level}
    (x : type-Large-Commutative-Monoid M l1)
    (y : type-Large-Commutative-Monoid M l2) →
    is-unit-Large-Commutative-Monoid x → mul-Large-Commutative-Monoid M x y ＝
    raise-Large-Commutative-Monoid M l1 y
  eq-left-is-unit-law-mul-Large-Commutative-Monoid =
    eq-left-is-unit-law-mul-Large-Monoid
      ( large-monoid-Large-Commutative-Monoid M)

  eq-right-is-unit-law-mul-Large-Commutative-Monoid :
    {l1 l2 : Level}
    (x : type-Large-Commutative-Monoid M l1)
    (y : type-Large-Commutative-Monoid M l2) →
    is-unit-Large-Commutative-Monoid y →
    mul-Large-Commutative-Monoid M x y ＝ raise-Large-Commutative-Monoid M l2 x
  eq-right-is-unit-law-mul-Large-Commutative-Monoid =
    eq-right-is-unit-law-mul-Large-Monoid
      ( large-monoid-Large-Commutative-Monoid M)

  sim-left-is-unit-law-mul-Large-Commutative-Monoid :
    {l1 l2 : Level}
    (x : type-Large-Commutative-Monoid M l1)
    (y : type-Large-Commutative-Monoid M l2) →
    is-unit-Large-Commutative-Monoid x →
    sim-Large-Commutative-Monoid M (mul-Large-Commutative-Monoid M x y) y
  sim-left-is-unit-law-mul-Large-Commutative-Monoid =
    sim-left-is-unit-law-mul-Large-Monoid
      ( large-monoid-Large-Commutative-Monoid M)

  sim-right-is-unit-law-mul-Large-Commutative-Monoid :
    {l1 l2 : Level}
    (x : type-Large-Commutative-Monoid M l1)
    (y : type-Large-Commutative-Monoid M l2) →
    is-unit-Large-Commutative-Monoid y →
    sim-Large-Commutative-Monoid M (mul-Large-Commutative-Monoid M x y) x
  sim-right-is-unit-law-mul-Large-Commutative-Monoid =
    sim-right-is-unit-law-mul-Large-Monoid
      ( large-monoid-Large-Commutative-Monoid M)
```

### Similarity reasoning on large groups

```agda
module
  similarity-reasoning-Large-Commutative-Monoid
    {α : Level → Level} {β : Level → Level → Level}
    (M : Large-Commutative-Monoid α β)
  where

  open
    similarity-reasoning-Large-Monoid
      ( large-monoid-Large-Commutative-Monoid M)
    public
```

### Small commutative monoids from large commutative monoids

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  where

  monoid-Large-Commutative-Monoid :
    (l : Level) → Monoid (α l)
  monoid-Large-Commutative-Monoid =
    monoid-Large-Monoid (large-monoid-Large-Commutative-Monoid M)

  commutative-monoid-Large-Commutative-Monoid :
    (l : Level) → Commutative-Monoid (α l)
  commutative-monoid-Large-Commutative-Monoid l =
    ( monoid-Large-Commutative-Monoid l ,
      commutative-mul-Large-Commutative-Monoid M)
```

### The raise operation is a commutative monoid homomorphism

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  (l1 l2 : Level)
  where

  hom-raise-Large-Commutative-Monoid :
    hom-Commutative-Monoid
      ( commutative-monoid-Large-Commutative-Monoid M l1)
      ( commutative-monoid-Large-Commutative-Monoid M (l1 ⊔ l2))
  hom-raise-Large-Commutative-Monoid =
    hom-raise-Large-Monoid (large-monoid-Large-Commutative-Monoid M) l1 l2
```

### Swapping laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  {l1 l2 l3 : Level}
  (x : type-Large-Commutative-Monoid M l1)
  (y : type-Large-Commutative-Monoid M l2)
  (z : type-Large-Commutative-Monoid M l3)
  (let _*M_ = mul-Large-Commutative-Monoid M)
  where

  abstract
    left-swap-mul-Large-Commutative-Monoid :
      mul-Large-Commutative-Monoid M x (mul-Large-Commutative-Monoid M y z) ＝
      mul-Large-Commutative-Monoid M y (mul-Large-Commutative-Monoid M x z)
    left-swap-mul-Large-Commutative-Monoid =
      equational-reasoning
        x *M (y *M z)
        ＝ (x *M y) *M z
          by inv (associative-mul-Large-Commutative-Monoid M x y z)
        ＝ (y *M x) *M z
          by
            ap-mul-Large-Commutative-Monoid M
              ( commutative-mul-Large-Commutative-Monoid M x y)
              ( refl)
        ＝ y *M (x *M z)
          by associative-mul-Large-Commutative-Monoid M y x z

    right-swap-mul-Large-Commutative-Monoid :
      mul-Large-Commutative-Monoid M (mul-Large-Commutative-Monoid M x y) z ＝
      mul-Large-Commutative-Monoid M (mul-Large-Commutative-Monoid M x z) y
    right-swap-mul-Large-Commutative-Monoid =
      equational-reasoning
        (x *M y) *M z
        ＝ x *M (y *M z)
          by associative-mul-Large-Commutative-Monoid M x y z
        ＝ x *M (z *M y)
          by
            ap-mul-Large-Commutative-Monoid M
              ( refl)
              ( commutative-mul-Large-Commutative-Monoid M y z)
        ＝ (x *M z) *M y
          by inv (associative-mul-Large-Commutative-Monoid M x z y)
```

### Interchange laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Commutative-Monoid α β)
  {l1 l2 l3 l4 : Level}
  (x : type-Large-Commutative-Monoid M l1)
  (y : type-Large-Commutative-Monoid M l2)
  (z : type-Large-Commutative-Monoid M l3)
  (w : type-Large-Commutative-Monoid M l4)
  (let _*M_ = mul-Large-Commutative-Monoid M)
  where

  abstract
    interchange-mul-mul-Large-Commutative-Monoid :
      mul-Large-Commutative-Monoid M
        ( mul-Large-Commutative-Monoid M x y)
        ( mul-Large-Commutative-Monoid M z w) ＝
      mul-Large-Commutative-Monoid M
        ( mul-Large-Commutative-Monoid M x z)
        ( mul-Large-Commutative-Monoid M y w)
    interchange-mul-mul-Large-Commutative-Monoid =
      equational-reasoning
        (x *M y) *M (z *M w)
        ＝ x *M (y *M (z *M w))
          by associative-mul-Large-Commutative-Monoid M x y (z *M w)
        ＝ x *M (z *M (y *M w))
          by
            ap-mul-Large-Commutative-Monoid M
              ( refl)
              ( left-swap-mul-Large-Commutative-Monoid M y z w)
        ＝ (x *M z) *M (y *M w)
          by inv (associative-mul-Large-Commutative-Monoid M x z (y *M w))
```
