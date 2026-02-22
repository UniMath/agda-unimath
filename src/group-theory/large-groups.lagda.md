# Large groups

```agda
module group-theory.large-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.cumulative-large-sets
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.identity-types
open import foundation.involutions
open import foundation.large-binary-relations
open import foundation.large-similarity-relations
open import foundation.logical-equivalences
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.sets
open import foundation.similarity-preserving-binary-maps-cumulative-large-sets
open import foundation.similarity-preserving-maps-cumulative-large-sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.large-monoids
open import group-theory.large-semigroups
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

A {{#concept "large group" Agda=Large-Group}} is a
[large monoid](group-theory.large-monoids.md) with an inverse operation `i`,
characterized by `i x ∙ x = x ∙ i x = e`, where `e` is the identity element.

## Definition

```agda
record Large-Group (α : Level → Level) (β : Level → Level → Level) : UUω where
  constructor
    make-Large-Group

  field
    large-monoid-Large-Group : Large-Monoid α β

  large-semigroup-Large-Group : Large-Semigroup α β
  large-semigroup-Large-Group =
    large-semigroup-Large-Monoid large-monoid-Large-Group

  cumulative-large-set-Large-Group : Cumulative-Large-Set α β
  cumulative-large-set-Large-Group =
    cumulative-large-set-Large-Monoid large-monoid-Large-Group

  type-Large-Group : (l : Level) → UU (α l)
  type-Large-Group = type-Large-Monoid large-monoid-Large-Group

  set-Large-Group : (l : Level) → Set (α l)
  set-Large-Group = set-Large-Monoid large-monoid-Large-Group

  mul-Large-Group :
    {l1 l2 : Level} → type-Large-Group l1 → type-Large-Group l2 →
    type-Large-Group (l1 ⊔ l2)
  mul-Large-Group = mul-Large-Monoid large-monoid-Large-Group

  mul-Large-Group' :
    {l1 l2 : Level} → type-Large-Group l1 → type-Large-Group l2 →
    type-Large-Group (l1 ⊔ l2)
  mul-Large-Group' x y = mul-Large-Group y x

  ap-mul-Large-Group :
    {l1 l2 : Level}
    {x x' : type-Large-Group l1} → x ＝ x' →
    {y y' : type-Large-Group l2} → y ＝ y' →
    mul-Large-Group x y ＝ mul-Large-Group x' y'
  ap-mul-Large-Group = ap-mul-Large-Monoid large-monoid-Large-Group

  field
    inv-Large-Group : {l : Level} → type-Large-Group l → type-Large-Group l

  is-unit-prop-Large-Group : {l : Level} → type-Large-Group l → Prop (β l lzero)
  is-unit-prop-Large-Group = is-unit-prop-Large-Monoid large-monoid-Large-Group

  is-unit-Large-Group : {l : Level} → type-Large-Group l → UU (β l lzero)
  is-unit-Large-Group = is-unit-Large-Monoid large-monoid-Large-Group

  field
    sim-left-inverse-law-mul-Large-Group :
      {l : Level} (x : type-Large-Group l) →
      is-unit-Large-Group (mul-Large-Group (inv-Large-Group x) x)

    sim-right-inverse-law-mul-Large-Group :
      {l : Level} (x : type-Large-Group l) →
      is-unit-Large-Group (mul-Large-Group x (inv-Large-Group x))

open Large-Group public
```

## Properties

### Similarity

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (G : Large-Group α β)
  where

  large-similarity-relation-Large-Group :
    Large-Similarity-Relation β (type-Large-Group G)
  large-similarity-relation-Large-Group =
    large-similarity-relation-Large-Monoid (large-monoid-Large-Group G)

  sim-prop-Large-Group :
    Large-Relation-Prop β (type-Large-Group G)
  sim-prop-Large-Group =
    sim-prop-Large-Monoid (large-monoid-Large-Group G)

  sim-Large-Group : Large-Relation β (type-Large-Group G)
  sim-Large-Group = sim-Large-Monoid (large-monoid-Large-Group G)

  refl-sim-Large-Group :
    is-reflexive-Large-Relation (type-Large-Group G) sim-Large-Group
  refl-sim-Large-Group =
    refl-sim-Large-Monoid (large-monoid-Large-Group G)

  symmetric-sim-Large-Group :
    is-symmetric-Large-Relation (type-Large-Group G) sim-Large-Group
  symmetric-sim-Large-Group =
    symmetric-sim-Large-Monoid (large-monoid-Large-Group G)

  transitive-sim-Large-Group :
    is-transitive-Large-Relation (type-Large-Group G) sim-Large-Group
  transitive-sim-Large-Group =
    transitive-sim-Large-Monoid (large-monoid-Large-Group G)

  sim-eq-Large-Group :
    {l : Level} {x y : type-Large-Group G l} → x ＝ y → sim-Large-Group x y
  sim-eq-Large-Group = sim-eq-Large-Monoid (large-monoid-Large-Group G)

  eq-sim-Large-Group :
    {l : Level} (x y : type-Large-Group G l) → sim-Large-Group x y → x ＝ y
  eq-sim-Large-Group = eq-sim-Large-Monoid (large-monoid-Large-Group G)
```

### Raising universe levels

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (G : Large-Group α β)
  where

  raise-Large-Group :
    {l0 : Level} (l : Level) →
    type-Large-Group G l0 → type-Large-Group G (l0 ⊔ l)
  raise-Large-Group = raise-Large-Monoid (large-monoid-Large-Group G)

  sim-raise-Large-Group :
    {l0 : Level} (l : Level) (x : type-Large-Group G l0) →
    sim-Large-Group G x (raise-Large-Group l x)
  sim-raise-Large-Group =
    sim-raise-Large-Monoid (large-monoid-Large-Group G)

  sim-raise-Large-Group' :
    {l0 : Level} (l : Level) (x : type-Large-Group G l0) →
    sim-Large-Group G (raise-Large-Group l x) x
  sim-raise-Large-Group' =
    sim-raise-Large-Monoid' (large-monoid-Large-Group G)

  eq-raise-Large-Group :
    {l : Level} (x : type-Large-Group G l) → raise-Large-Group l x ＝ x
  eq-raise-Large-Group =
    eq-raise-Large-Monoid (large-monoid-Large-Group G)

  eq-raise-leq-level-Large-Group :
    (l1 : Level) {l2 : Level} (x : type-Large-Group G (l1 ⊔ l2)) →
    raise-Large-Group l2 x ＝ x
  eq-raise-leq-level-Large-Group =
    eq-raise-leq-level-Large-Monoid (large-monoid-Large-Group G)

  is-emb-raise-Large-Group :
    (l1 l2 : Level) → is-emb (raise-Large-Group {l1} l2)
  is-emb-raise-Large-Group =
    is-emb-raise-Large-Monoid (large-monoid-Large-Group G)

  emb-raise-Large-Group :
    (l1 l2 : Level) → type-Large-Group G l1 ↪ type-Large-Group G (l1 ⊔ l2)
  emb-raise-Large-Group =
    emb-raise-Large-Monoid (large-monoid-Large-Group G)

  raise-raise-Large-Group :
    {l0 l1 l2 : Level} (x : type-Large-Group G l0) →
    raise-Large-Group l1 (raise-Large-Group l2 x) ＝
    raise-Large-Group (l1 ⊔ l2) x
  raise-raise-Large-Group =
    raise-raise-Large-Monoid (large-monoid-Large-Group G)

  eq-raise-sim-Large-Group :
    {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
    sim-Large-Group G x y → raise-Large-Group l2 x ＝ raise-Large-Group l1 y
  eq-raise-sim-Large-Group =
    eq-raise-sim-Large-Monoid (large-monoid-Large-Group G)

  sim-eq-raise-Large-Group :
    {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
    raise-Large-Group l2 x ＝ raise-Large-Group l1 y → sim-Large-Group G x y
  sim-eq-raise-Large-Group =
    sim-eq-raise-Large-Monoid (large-monoid-Large-Group G)

  eq-raise-iff-sim-Large-Group :
    {l1 l2 : Level}
    (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
    ( sim-Large-Group G x y ↔
      ( raise-Large-Group l2 x ＝ raise-Large-Group l1 y))
  eq-raise-iff-sim-Large-Group =
    eq-raise-iff-sim-Large-Monoid (large-monoid-Large-Group G)

  eq-raise-sim-Large-Group' :
    {l1 l2 : Level}
    (x : type-Large-Group G (l1 ⊔ l2)) (y : type-Large-Group G l2) →
    sim-Large-Group G x y → x ＝ raise-Large-Group l1 y
  eq-raise-sim-Large-Group' =
    eq-raise-sim-Large-Monoid' (large-monoid-Large-Group G)
```

### Similarity preservation of multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  sim-preserving-binary-operator-mul-Large-Group :
    sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Group G)
  sim-preserving-binary-operator-mul-Large-Group =
    sim-preserving-binary-operator-mul-Large-Monoid (large-monoid-Large-Group G)

  preserves-sim-mul-Large-Group :
    preserves-sim-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Group G)
      ( mul-Large-Group G)
  preserves-sim-mul-Large-Group =
    preserves-sim-mul-Large-Monoid (large-monoid-Large-Group G)

  sim-preserving-map-left-mul-Large-Group :
    {l : Level} (x : type-Large-Group G l) →
    sim-preserving-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Group G)
  sim-preserving-map-left-mul-Large-Group =
    sim-preserving-map-left-mul-Large-Monoid (large-monoid-Large-Group G)

  preserves-sim-left-mul-Large-Group :
    {l : Level} (x : type-Large-Group G l) →
    preserves-sim-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Group G)
      ( mul-Large-Group G x)
  preserves-sim-left-mul-Large-Group =
    preserves-sim-left-mul-Large-Monoid (large-monoid-Large-Group G)

  sim-preserving-map-right-mul-Large-Group :
    {l : Level} (y : type-Large-Group G l) →
    sim-preserving-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Group G)
  sim-preserving-map-right-mul-Large-Group =
    sim-preserving-map-right-mul-Large-Monoid
      ( large-monoid-Large-Group G)

  preserves-sim-right-mul-Large-Group :
    {l : Level} (y : type-Large-Group G l) →
    preserves-sim-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Group G)
      ( mul-Large-Group' G y)
  preserves-sim-right-mul-Large-Group =
    preserves-sim-right-mul-Large-Monoid (large-monoid-Large-Group G)
```

### Raising universe levels in multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    mul-raise-right-Large-Group :
      {l1 l2 : Level} (l3 : Level) →
      (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      mul-Large-Group G x (raise-Large-Group G l3 y) ＝
      raise-Large-Group G l3 (mul-Large-Group G x y)
    mul-raise-right-Large-Group =
      mul-raise-right-Large-Monoid (large-monoid-Large-Group G)

    mul-raise-left-Large-Group :
      {l1 l2 : Level} (l3 : Level) →
      (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      mul-Large-Group G (raise-Large-Group G l3 x) y ＝
      raise-Large-Group G l3 (mul-Large-Group G x y)
    mul-raise-left-Large-Group =
      mul-raise-left-Large-Monoid (large-monoid-Large-Group G)

    mul-raise-raise-Large-Group :
      {l1 l2 : Level} (l3 l4 : Level) →
      (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      mul-Large-Group G
        ( raise-Large-Group G l3 x)
        ( raise-Large-Group G l4 y) ＝
      raise-Large-Group G (l3 ⊔ l4) (mul-Large-Group G x y)
    mul-raise-raise-Large-Group =
      mul-raise-raise-Large-Monoid (large-monoid-Large-Group G)
```

### Semigroup laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  associative-mul-Large-Group :
    {l1 l2 l3 : Level}
    (x : type-Large-Group G l1)
    (y : type-Large-Group G l2)
    (z : type-Large-Group G l3) →
    mul-Large-Group G (mul-Large-Group G x y) z ＝
    mul-Large-Group G x (mul-Large-Group G y z)
  associative-mul-Large-Group =
    associative-mul-Large-Monoid (large-monoid-Large-Group G)
```

### Monoid laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  unit-Large-Group : type-Large-Group G lzero
  unit-Large-Group = unit-Large-Monoid (large-monoid-Large-Group G)

  raise-unit-Large-Group : (l : Level) → type-Large-Group G l
  raise-unit-Large-Group = raise-unit-Large-Monoid (large-monoid-Large-Group G)

  raise-unit-lzero-Large-Group :
    raise-unit-Large-Group lzero ＝ unit-Large-Group
  raise-unit-lzero-Large-Group =
    raise-unit-lzero-Large-Monoid (large-monoid-Large-Group G)

  is-unit-unit-Large-Group : is-unit-Large-Group G unit-Large-Group
  is-unit-unit-Large-Group =
    is-unit-unit-Large-Monoid (large-monoid-Large-Group G)

  is-unit-raise-unit-Large-Group :
    (l : Level) → is-unit-Large-Group G (raise-unit-Large-Group l)
  is-unit-raise-unit-Large-Group =
    is-unit-raise-unit-Large-Monoid (large-monoid-Large-Group G)

  eq-raise-unit-is-unit-Large-Group :
    {l : Level} (x : type-Large-Group G l) →
    is-unit-Large-Group G x → x ＝ raise-unit-Large-Group l
  eq-raise-unit-is-unit-Large-Group =
    eq-raise-unit-is-unit-Large-Monoid (large-monoid-Large-Group G)

  left-unit-law-mul-Large-Group :
    {l : Level} (x : type-Large-Group G l) →
    mul-Large-Group G unit-Large-Group x ＝ x
  left-unit-law-mul-Large-Group =
    left-unit-law-mul-Large-Monoid (large-monoid-Large-Group G)

  right-unit-law-mul-Large-Group :
    {l : Level} (x : type-Large-Group G l) →
    mul-Large-Group G x unit-Large-Group ＝ x
  right-unit-law-mul-Large-Group =
    right-unit-law-mul-Large-Monoid (large-monoid-Large-Group G)

  left-raise-unit-law-mul-Large-Group :
    {l1 l2 : Level} (y : type-Large-Group G l2) →
    mul-Large-Group G (raise-unit-Large-Group l1) y ＝ raise-Large-Group G l1 y
  left-raise-unit-law-mul-Large-Group =
    left-raise-unit-law-mul-Large-Monoid (large-monoid-Large-Group G)

  right-raise-unit-law-mul-Large-Group :
    {l1 l2 : Level} (x : type-Large-Group G l1) →
    mul-Large-Group G x (raise-unit-Large-Group l2) ＝
    raise-Large-Group G l2 x
  right-raise-unit-law-mul-Large-Group =
    right-raise-unit-law-mul-Large-Monoid (large-monoid-Large-Group G)

  eq-left-is-unit-law-mul-Large-Group :
    {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
    is-unit-Large-Group G x → mul-Large-Group G x y ＝ raise-Large-Group G l1 y
  eq-left-is-unit-law-mul-Large-Group =
    eq-left-is-unit-law-mul-Large-Monoid (large-monoid-Large-Group G)

  eq-right-is-unit-law-mul-Large-Group :
    {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
    is-unit-Large-Group G y → mul-Large-Group G x y ＝ raise-Large-Group G l2 x
  eq-right-is-unit-law-mul-Large-Group =
    eq-right-is-unit-law-mul-Large-Monoid (large-monoid-Large-Group G)

  sim-left-is-unit-law-mul-Large-Group :
    {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
    is-unit-Large-Group G x → sim-Large-Group G (mul-Large-Group G x y) y
  sim-left-is-unit-law-mul-Large-Group =
    sim-left-is-unit-law-mul-Large-Monoid (large-monoid-Large-Group G)

  sim-right-is-unit-law-mul-Large-Group :
    {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
    is-unit-Large-Group G y → sim-Large-Group G (mul-Large-Group G x y) x
  sim-right-is-unit-law-mul-Large-Group =
    sim-right-is-unit-law-mul-Large-Monoid (large-monoid-Large-Group G)
```

### Similarity reasoning on large groups

```agda
module
  similarity-reasoning-Large-Group
    {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  open similarity-reasoning-Large-Monoid (large-monoid-Large-Group G) public
```

### Inverse laws in terms of equality

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    eq-left-inverse-law-mul-Large-Group :
      {l : Level} (x : type-Large-Group G l) →
      mul-Large-Group G (inv-Large-Group G x) x ＝ raise-unit-Large-Group G l
    eq-left-inverse-law-mul-Large-Group x =
      eq-raise-unit-is-unit-Large-Group G
        ( mul-Large-Group G (inv-Large-Group G x) x)
        ( sim-left-inverse-law-mul-Large-Group G x)

    eq-right-inverse-law-mul-Large-Group :
      {l : Level} (x : type-Large-Group G l) →
      mul-Large-Group G x (inv-Large-Group G x) ＝ raise-unit-Large-Group G l
    eq-right-inverse-law-mul-Large-Group x =
      eq-raise-unit-is-unit-Large-Group G
        ( mul-Large-Group G x (inv-Large-Group G x))
        ( sim-right-inverse-law-mul-Large-Group G x)
```

### Cancellation laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2)
  (let _*G_ = mul-Large-Group G) (let inv-G = inv-Large-Group G)
  where

  open similarity-reasoning-Large-Group G

  abstract
    sim-cancel-left-div-mul-Large-Group :
      sim-Large-Group G
        ( mul-Large-Group G (inv-Large-Group G x) (mul-Large-Group G x y))
        ( y)
    sim-cancel-left-div-mul-Large-Group =
      similarity-reasoning
        inv-G x *G (x *G y)
        ~ (inv-G x *G x) *G y
          by
            sim-eq-Large-Group G
              ( inv (associative-mul-Large-Group G (inv-G x) x y))
        ~ y
          by
            sim-left-is-unit-law-mul-Large-Group G _ y
              ( sim-left-inverse-law-mul-Large-Group G x)

    sim-cancel-left-mul-div-Large-Group :
      sim-Large-Group G
        ( mul-Large-Group G x (mul-Large-Group G (inv-Large-Group G x) y))
        ( y)
    sim-cancel-left-mul-div-Large-Group =
      similarity-reasoning
        x *G (inv-G x *G y)
        ~ (x *G inv-G x) *G y
          by
            sim-eq-Large-Group G
              ( inv (associative-mul-Large-Group G x (inv-G x) y))
        ~ y
          by
            sim-left-is-unit-law-mul-Large-Group G _ y
              ( sim-right-inverse-law-mul-Large-Group G x)

    sim-cancel-right-mul-div-Large-Group :
      sim-Large-Group G
        ( mul-Large-Group G (mul-Large-Group G y x) (inv-Large-Group G x))
        ( y)
    sim-cancel-right-mul-div-Large-Group =
      similarity-reasoning
        (y *G x) *G inv-G x
        ~ y *G (x *G inv-G x)
          by sim-eq-Large-Group G (associative-mul-Large-Group G y x (inv-G x))
        ~ y
          by
            sim-right-is-unit-law-mul-Large-Group G y _
              ( sim-right-inverse-law-mul-Large-Group G x)

    sim-cancel-right-div-mul-Large-Group :
      sim-Large-Group G
        ( mul-Large-Group G (mul-Large-Group G y (inv-Large-Group G x)) x)
        ( y)
    sim-cancel-right-div-mul-Large-Group =
      similarity-reasoning
        (y *G inv-G x) *G x
        ~ y *G (inv-G x *G x)
          by sim-eq-Large-Group G (associative-mul-Large-Group G y (inv-G x) x)
        ~ y
          by
            sim-right-is-unit-law-mul-Large-Group G y _
              ( sim-left-inverse-law-mul-Large-Group G x)

    eq-cancel-left-div-mul-Large-Group :
      mul-Large-Group G
        ( inv-Large-Group G x)
        ( mul-Large-Group G x y) ＝
      raise-Large-Group G l1 y
    eq-cancel-left-div-mul-Large-Group =
      eq-raise-sim-Large-Group' G _ _ sim-cancel-left-div-mul-Large-Group

    eq-cancel-left-mul-div-Large-Group :
      mul-Large-Group G
        ( x)
        ( mul-Large-Group G (inv-Large-Group G x) y) ＝
      raise-Large-Group G l1 y
    eq-cancel-left-mul-div-Large-Group =
      eq-raise-sim-Large-Group' G _ _ sim-cancel-left-mul-div-Large-Group

    eq-cancel-right-mul-div-Large-Group :
      mul-Large-Group G (mul-Large-Group G y x) (inv-Large-Group G x) ＝
      raise-Large-Group G l1 y
    eq-cancel-right-mul-div-Large-Group =
      eq-raise-sim-Large-Group' G _ _ sim-cancel-right-mul-div-Large-Group

    eq-cancel-right-div-mul-Large-Group :
      mul-Large-Group G (mul-Large-Group G y (inv-Large-Group G x)) x ＝
      raise-Large-Group G l1 y
    eq-cancel-right-div-mul-Large-Group =
      eq-raise-sim-Large-Group' G _ _ sim-cancel-right-div-mul-Large-Group
```

### Uniqueness of inverses

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  (let inv-G = inv-Large-Group G)
  (let _*G_ = mul-Large-Group G)
  where

  open similarity-reasoning-Large-Group G

  abstract
    unique-right-inv-Large-Group :
      {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      is-unit-Large-Group G (mul-Large-Group G x y) →
      sim-Large-Group G y (inv-Large-Group G x)
    unique-right-inv-Large-Group x y xy~1 =
      similarity-reasoning
        y
        ~ inv-G x *G (x *G y)
          by
            symmetric-sim-Large-Group G _ _
              ( sim-cancel-left-div-mul-Large-Group G x y)
        ~ inv-G x
          by sim-right-is-unit-law-mul-Large-Group G (inv-G x) (x *G y) xy~1

    unique-left-inv-Large-Group :
      {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      is-unit-Large-Group G (mul-Large-Group G x y) →
      sim-Large-Group G x (inv-Large-Group G y)
    unique-left-inv-Large-Group x y xy~1 =
      similarity-reasoning
        x
        ~ (x *G y) *G inv-G y
          by
            symmetric-sim-Large-Group G _ _
              ( sim-cancel-right-mul-div-Large-Group G y x)
        ~ inv-G y
          by sim-left-is-unit-law-mul-Large-Group G (x *G y) (inv-G y) xy~1
```

### The inverse operation preserves similarity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  (let inv-G = inv-Large-Group G)
  (let _*G_ = mul-Large-Group G)
  where

  open similarity-reasoning-Large-Group G

  abstract
    preserves-sim-inv-Large-Group :
      preserves-sim-endomap-Cumulative-Large-Set
        ( id)
        ( cumulative-large-set-Large-Group G)
        ( inv-Large-Group G)
    preserves-sim-inv-Large-Group x y x~y =
      unique-left-inv-Large-Group G
        ( inv-G x)
        ( y)
        ( similarity-reasoning
          inv-G x *G y
          ~ inv-G x *G x
            by
              preserves-sim-left-mul-Large-Group G
                ( inv-G x)
                ( y)
                ( x)
                ( symmetric-sim-Large-Group G x y x~y)
          ~ unit-Large-Group G
            by sim-left-inverse-law-mul-Large-Group G x)

  sim-preserving-endomap-inv-Large-Group :
    sim-preserving-endomap-Cumulative-Large-Set
      ( id)
      ( cumulative-large-set-Large-Group G)
  sim-preserving-endomap-inv-Large-Group =
    make-sim-preserving-endomap-Cumulative-Large-Set
      ( id)
      ( cumulative-large-set-Large-Group G)
      ( inv-Large-Group G)
      ( preserves-sim-inv-Large-Group)
```

### Raising universe levels in the inverse operation

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    inv-raise-Large-Group :
      {l0 : Level} (l : Level) (x : type-Large-Group G l0) →
      inv-Large-Group G (raise-Large-Group G l x) ＝
      raise-Large-Group G l (inv-Large-Group G x)
    inv-raise-Large-Group =
      commute-map-raise-sim-preserving-endomap-Cumulative-Large-Set
        ( cumulative-large-set-Large-Group G)
        ( sim-preserving-endomap-inv-Large-Group G)
```

### Distributivity of inverses over multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    distributive-inv-mul-Large-Group :
      {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      inv-Large-Group G (mul-Large-Group G x y) ＝
      mul-Large-Group G (inv-Large-Group G y) (inv-Large-Group G x)
    distributive-inv-mul-Large-Group {l1} {l2} x y =
      let
        _*G_ = mul-Large-Group G
        inv-G = inv-Large-Group G
        open similarity-reasoning-Large-Group G
      in
        inv
          ( eq-sim-Large-Group G
            ( inv-G y *G inv-G x)
            ( inv-G (x *G y))
            ( unique-right-inv-Large-Group G _ _
              ( similarity-reasoning
                (x *G y) *G (inv-G y *G inv-G x)
                ~ x *G (y *G (inv-G y *G inv-G x))
                  by sim-eq-Large-Group G (associative-mul-Large-Group G _ _ _)
                ~ x *G inv-G x
                  by
                    preserves-sim-left-mul-Large-Group G
                      ( x)
                      ( y *G (inv-G y *G inv-G x))
                      ( inv-G x)
                      ( sim-cancel-left-mul-div-Large-Group G y (inv-G x))
                ~ unit-Large-Group G
                  by sim-right-inverse-law-mul-Large-Group G x)))
```

### Small groups from large groups

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  semigroup-Large-Group : (l : Level) → Semigroup (α l)
  semigroup-Large-Group =
    semigroup-Large-Monoid (large-monoid-Large-Group G)

  monoid-Large-Group : (l : Level) → Monoid (α l)
  monoid-Large-Group =
    monoid-Large-Monoid (large-monoid-Large-Group G)

  group-Large-Group : (l : Level) → Group (α l)
  group-Large-Group l =
    ( semigroup-Large-Group l ,
      ( raise-unit-Large-Group G l ,
        left-unit-law-mul-Monoid (monoid-Large-Group l) ,
        right-unit-law-mul-Monoid (monoid-Large-Group l)) ,
      inv-Large-Group G ,
      eq-left-inverse-law-mul-Large-Group G ,
      eq-right-inverse-law-mul-Large-Group G)
```

### The inverse of the identity is the identity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    inv-raise-unit-Large-Group :
      (l : Level) →
      inv-Large-Group G (raise-unit-Large-Group G l) ＝
      raise-unit-Large-Group G l
    inv-raise-unit-Large-Group l =
      inv-unit-Group (group-Large-Group G l)

    inv-is-unit-Large-Group :
      {l : Level} (x : type-Large-Group G l) →
      is-unit-Large-Group G x → is-unit-Large-Group G (inv-Large-Group G x)
    inv-is-unit-Large-Group {l} x x~1 =
      inv-tr
        ( is-unit-Large-Group G)
        ( inv-tr
          ( λ z → inv-Large-Group G z ＝ z)
          ( eq-raise-unit-is-unit-Large-Group G x x~1)
          ( inv-raise-unit-Large-Group l))
        ( x~1)

    inv-unit-Large-Group :
      inv-Large-Group G (unit-Large-Group G) ＝ unit-Large-Group G
    inv-unit-Large-Group =
      tr
        ( λ z → inv-Large-Group G z ＝ z)
        ( raise-unit-lzero-Large-Group G)
        ( inv-raise-unit-Large-Group lzero)
```

### Inverting elements of a large group is an involution

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    inv-inv-Large-Group :
      {l : Level} (x : type-Large-Group G l) →
      inv-Large-Group G (inv-Large-Group G x) ＝ x
    inv-inv-Large-Group {l} = inv-inv-Group (group-Large-Group G l)

  aut-inv-Large-Group : (l : Level) → Aut (type-Large-Group G l)
  aut-inv-Large-Group l =
    ( inv-Large-Group G ,
      is-equiv-is-involution inv-inv-Large-Group)
```

### Right multiplication reflects similarity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  {l1 l2 l3 : Level}
  (x : type-Large-Group G l1)
  (y : type-Large-Group G l2)
  (z : type-Large-Group G l3)
  where

  abstract
    reflects-sim-right-mul-Large-Group :
      sim-Large-Group G
        ( mul-Large-Group G x z)
        ( mul-Large-Group G y z) →
      sim-Large-Group G x y
    reflects-sim-right-mul-Large-Group xz~yz =
      let
        _*G_ = mul-Large-Group G
        inv-G = inv-Large-Group G
        open similarity-reasoning-Large-Group G
      in
        similarity-reasoning
          x
          ~ (x *G z) *G inv-G z
            by
              symmetric-sim-Large-Group G _ _
                ( sim-cancel-right-mul-div-Large-Group G z x)
          ~ (y *G z) *G inv-G z
            by
              preserves-sim-right-mul-Large-Group G
                ( inv-G z)
                ( x *G z)
                ( y *G z)
                ( xz~yz)
          ~ y
            by sim-cancel-right-mul-div-Large-Group G z y
```

### Left multiplication reflects similarity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  {l1 l2 l3 : Level}
  (x : type-Large-Group G l1)
  (y : type-Large-Group G l2)
  (z : type-Large-Group G l3)
  where

  abstract
    reflects-sim-left-mul-Large-Group :
      sim-Large-Group G
        ( mul-Large-Group G x y)
        ( mul-Large-Group G x z) →
      sim-Large-Group G y z
    reflects-sim-left-mul-Large-Group xy~xz =
      let
        _*G_ = mul-Large-Group G
        inv-G = inv-Large-Group G
        open similarity-reasoning-Large-Group G
      in
        similarity-reasoning
          y
          ~ inv-G x *G (x *G y)
            by
              symmetric-sim-Large-Group G _ _
                ( sim-cancel-left-div-mul-Large-Group G x y)
          ~ inv-G x *G (x *G z)
            by
              preserves-sim-left-mul-Large-Group G
                ( inv-G x)
                ( x *G y)
                ( x *G z)
                ( xy~xz)
          ~ z
            by sim-cancel-left-div-mul-Large-Group G x z
```

### Left multiplication by an element of a large group is an embedding

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  {l1 : Level} (l2 : Level) (x : type-Large-Group G l1)
  (let inv-G = inv-Large-Group G)
  (let _*G_ = mul-Large-Group G)
  where

  abstract
    all-elements-equal-fiber-left-mul-Large-Group :
      (y : type-Large-Group G (l1 ⊔ l2)) →
      all-elements-equal (fiber (mul-Large-Group G {l2 = l2} x) y)
    all-elements-equal-fiber-left-mul-Large-Group y (a , xa=y) (b , xb=y) =
      eq-type-subtype
        ( λ c → Id-Prop (set-Large-Group G (l1 ⊔ l2)) (x *G c) y)
        ( eq-sim-Large-Group G a b
          ( reflects-sim-left-mul-Large-Group G x a b
            ( sim-eq-Large-Group G (xa=y ∙ inv xb=y))))

    is-prop-map-left-mul-Large-Group :
      is-prop-map (mul-Large-Group G {l2 = l2} x)
    is-prop-map-left-mul-Large-Group y =
      is-prop-all-elements-equal
        ( all-elements-equal-fiber-left-mul-Large-Group y)

    is-emb-left-mul-Large-Group : is-emb (mul-Large-Group G {l2 = l2} x)
    is-emb-left-mul-Large-Group =
      is-emb-is-prop-map is-prop-map-left-mul-Large-Group

  emb-left-mul-Large-Group :
    type-Large-Group G l2 ↪ type-Large-Group G (l1 ⊔ l2)
  emb-left-mul-Large-Group =
    ( mul-Large-Group G x , is-emb-left-mul-Large-Group)
```

### Right multiplication by an element of a large group is an embedding

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  {l1 : Level} (l2 : Level) (x : type-Large-Group G l1)
  (let inv-G = inv-Large-Group G)
  (let _*G_ = mul-Large-Group G)
  where

  abstract
    all-elements-equal-fiber-right-mul-Large-Group :
      (y : type-Large-Group G (l1 ⊔ l2)) →
      all-elements-equal (fiber (mul-Large-Group' G {l2 = l2} x) y)
    all-elements-equal-fiber-right-mul-Large-Group y (a , ax=y) (b , bx=y) =
      eq-type-subtype
        ( λ z → Id-Prop (set-Large-Group G (l1 ⊔ l2)) (z *G x) y)
        ( eq-sim-Large-Group G a b
          ( reflects-sim-right-mul-Large-Group G a b x
            ( sim-eq-Large-Group G (ax=y ∙ inv bx=y))))

    is-prop-map-right-mul-Large-Group :
      is-prop-map (mul-Large-Group' G {l2 = l2} x)
    is-prop-map-right-mul-Large-Group y =
      is-prop-all-elements-equal
        ( all-elements-equal-fiber-right-mul-Large-Group y)

    is-emb-right-mul-Large-Group : is-emb (mul-Large-Group' G {l2 = l2} x)
    is-emb-right-mul-Large-Group =
      is-emb-is-prop-map is-prop-map-right-mul-Large-Group

  emb-right-mul-Large-Group :
    type-Large-Group G l2 ↪ type-Large-Group G (l1 ⊔ l2)
  emb-right-mul-Large-Group =
    ( mul-Large-Group' G x , is-emb-right-mul-Large-Group)
```

### The raise operation is a group homomorphism

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  (l1 l2 : Level)
  where

  hom-raise-Large-Group :
    hom-Group
      ( group-Large-Group G l1)
      ( group-Large-Group G (l1 ⊔ l2))
  hom-raise-Large-Group =
    ( raise-Large-Group G l2 ,
      λ {x} {y} → inv (mul-raise-raise-Large-Group G l2 l2 x y))
```

### `x² = x` if and only if `x` is a unit

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    eq-raise-unit-is-idempotent-Large-Group :
      {l : Level} (x : type-Large-Group G l) →
      mul-Large-Group G x x ＝ x → x ＝ raise-unit-Large-Group G l
    eq-raise-unit-is-idempotent-Large-Group {l} _ =
      is-unit-is-idempotent-Group (group-Large-Group G l)

    is-unit-is-idempotent-Large-Group :
      {l : Level} (x : type-Large-Group G l) →
      mul-Large-Group G x x ＝ x → is-unit-Large-Group G x
    is-unit-is-idempotent-Large-Group {l} x x²=x =
      inv-tr
        ( is-unit-Large-Group G)
        ( eq-raise-unit-is-idempotent-Large-Group x x²=x)
        ( is-unit-raise-unit-Large-Group G l)

    is-idempotent-mul-is-unit-Large-Group :
      {l : Level} (x : type-Large-Group G l) →
      is-unit-Large-Group G x → mul-Large-Group G x x ＝ x
    is-idempotent-mul-is-unit-Large-Group x x~1 =
      eq-sim-Large-Group G _ _ (sim-left-is-unit-law-mul-Large-Group G x x x~1)
```
