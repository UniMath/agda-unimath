# Large monoids

```agda
module group-theory.large-monoids where
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
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.homomorphisms-monoids
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
    large-semigroup-Large-Monoid : Large-Semigroup α β

  cumulative-large-set-Large-Monoid : Cumulative-Large-Set α β
  cumulative-large-set-Large-Monoid =
    cumulative-large-set-Large-Semigroup large-semigroup-Large-Monoid

  set-Large-Monoid : (l : Level) → Set (α l)
  set-Large-Monoid = set-Large-Semigroup large-semigroup-Large-Monoid

  type-Large-Monoid : (l : Level) → UU (α l)
  type-Large-Monoid = type-Large-Semigroup large-semigroup-Large-Monoid

  mul-Large-Monoid :
    {l1 l2 : Level} → type-Large-Monoid l1 → type-Large-Monoid l2 →
    type-Large-Monoid (l1 ⊔ l2)
  mul-Large-Monoid =
    mul-Large-Semigroup large-semigroup-Large-Monoid

  mul-Large-Monoid' :
    {l1 l2 : Level} → type-Large-Monoid l1 → type-Large-Monoid l2 →
    type-Large-Monoid (l1 ⊔ l2)
  mul-Large-Monoid' y x = mul-Large-Monoid x y

  ap-mul-Large-Monoid :
    {l1 l2 : Level} →
    {x x' : type-Large-Monoid l1} → x ＝ x' →
    {y y' : type-Large-Monoid l2} → y ＝ y' →
    mul-Large-Monoid x y ＝ mul-Large-Monoid x' y'
  ap-mul-Large-Monoid = ap-binary mul-Large-Monoid

  field
    unit-Large-Monoid : type-Large-Monoid lzero
    left-unit-law-mul-Large-Monoid :
      {l : Level} (x : type-Large-Monoid l) →
      mul-Large-Monoid unit-Large-Monoid x ＝ x
    right-unit-law-mul-Large-Monoid :
      {l : Level} (x : type-Large-Monoid l) →
      mul-Large-Monoid x unit-Large-Monoid ＝ x

  associative-mul-Large-Monoid :
    {l1 l2 l3 : Level} →
    (x : type-Large-Monoid l1) (y : type-Large-Monoid l2)
    (z : type-Large-Monoid l3) →
    mul-Large-Monoid (mul-Large-Monoid x y) z ＝
    mul-Large-Monoid x (mul-Large-Monoid y z)
  associative-mul-Large-Monoid =
    associative-mul-Large-Semigroup large-semigroup-Large-Monoid

open Large-Monoid public
```

## Properties

### Similarity in a large monoid

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (M : Large-Monoid α β)
  where

  large-similarity-relation-Large-Monoid :
    Large-Similarity-Relation β (type-Large-Monoid M)
  large-similarity-relation-Large-Monoid =
    large-similarity-relation-Large-Semigroup (large-semigroup-Large-Monoid M)

  sim-prop-Large-Monoid :
    Large-Relation-Prop β (type-Large-Monoid M)
  sim-prop-Large-Monoid =
    sim-prop-Large-Semigroup (large-semigroup-Large-Monoid M)

  sim-Large-Monoid :
    Large-Relation β (type-Large-Monoid M)
  sim-Large-Monoid = sim-Large-Semigroup (large-semigroup-Large-Monoid M)

  refl-sim-Large-Monoid :
    is-reflexive-Large-Relation (type-Large-Monoid M) sim-Large-Monoid
  refl-sim-Large-Monoid =
    refl-sim-Large-Semigroup (large-semigroup-Large-Monoid M)

  symmetric-sim-Large-Monoid :
    is-symmetric-Large-Relation (type-Large-Monoid M) sim-Large-Monoid
  symmetric-sim-Large-Monoid =
    symmetric-sim-Large-Semigroup (large-semigroup-Large-Monoid M)

  transitive-sim-Large-Monoid :
    is-transitive-Large-Relation (type-Large-Monoid M) sim-Large-Monoid
  transitive-sim-Large-Monoid =
    transitive-sim-Large-Semigroup (large-semigroup-Large-Monoid M)

  sim-eq-Large-Monoid :
    {l : Level} {x y : type-Large-Monoid M l} →
    x ＝ y → sim-Large-Monoid x y
  sim-eq-Large-Monoid = sim-eq-Large-Semigroup (large-semigroup-Large-Monoid M)

  eq-sim-Large-Monoid :
    {l : Level} (x y : type-Large-Monoid M l) →
    sim-Large-Monoid x y → x ＝ y
  eq-sim-Large-Monoid = eq-sim-Large-Semigroup (large-semigroup-Large-Monoid M)
```

### Raising universe levels in a large monoid

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (M : Large-Monoid α β)
  where

  raise-Large-Monoid :
    {l0 : Level} (l : Level) →
    type-Large-Monoid M l0 → type-Large-Monoid M (l0 ⊔ l)
  raise-Large-Monoid = raise-Large-Semigroup (large-semigroup-Large-Monoid M)

  sim-raise-Large-Monoid :
    {l0 : Level} (l : Level) (x : type-Large-Monoid M l0) →
    sim-Large-Monoid M x (raise-Large-Monoid l x)
  sim-raise-Large-Monoid =
    sim-raise-Large-Semigroup (large-semigroup-Large-Monoid M)

  sim-raise-Large-Monoid' :
    {l0 : Level} (l : Level) (x : type-Large-Monoid M l0) →
    sim-Large-Monoid M (raise-Large-Monoid l x) x
  sim-raise-Large-Monoid' =
    sim-raise-Large-Semigroup' (large-semigroup-Large-Monoid M)

  eq-raise-Large-Monoid :
    {l : Level} (x : type-Large-Monoid M l) → raise-Large-Monoid l x ＝ x
  eq-raise-Large-Monoid =
    eq-raise-Large-Semigroup (large-semigroup-Large-Monoid M)

  eq-raise-leq-level-Large-Monoid :
    (l1 : Level) {l2 : Level} (x : type-Large-Monoid M (l1 ⊔ l2)) →
    raise-Large-Monoid l2 x ＝ x
  eq-raise-leq-level-Large-Monoid =
    eq-raise-leq-level-Large-Semigroup (large-semigroup-Large-Monoid M)

  is-emb-raise-Large-Monoid :
    (l1 l2 : Level) → is-emb (raise-Large-Monoid {l1} l2)
  is-emb-raise-Large-Monoid =
    is-emb-raise-Large-Semigroup (large-semigroup-Large-Monoid M)

  emb-raise-Large-Monoid :
    (l1 l2 : Level) → type-Large-Monoid M l1 ↪ type-Large-Monoid M (l1 ⊔ l2)
  emb-raise-Large-Monoid =
    emb-raise-Large-Semigroup (large-semigroup-Large-Monoid M)

  raise-raise-Large-Monoid :
    {l0 : Level} (l1 l2 : Level) (x : type-Large-Monoid M l0) →
    raise-Large-Monoid l1 (raise-Large-Monoid l2 x) ＝
    raise-Large-Monoid (l1 ⊔ l2) x
  raise-raise-Large-Monoid =
    raise-raise-Large-Semigroup (large-semigroup-Large-Monoid M)

  eq-raise-sim-Large-Monoid :
    {l1 l2 : Level} (x : type-Large-Monoid M l1) (y : type-Large-Monoid M l2) →
    sim-Large-Monoid M x y → raise-Large-Monoid l2 x ＝ raise-Large-Monoid l1 y
  eq-raise-sim-Large-Monoid =
    eq-raise-sim-Large-Semigroup (large-semigroup-Large-Monoid M)

  sim-eq-raise-Large-Monoid :
    {l1 l2 : Level} (x : type-Large-Monoid M l1) (y : type-Large-Monoid M l2) →
    raise-Large-Monoid l2 x ＝ raise-Large-Monoid l1 y → sim-Large-Monoid M x y
  sim-eq-raise-Large-Monoid =
    sim-eq-raise-Large-Semigroup (large-semigroup-Large-Monoid M)

  eq-raise-iff-sim-Large-Monoid :
    {l1 l2 : Level} →
    (x : type-Large-Monoid M l1) (y : type-Large-Monoid M l2) →
    ( sim-Large-Monoid M x y ↔
      ( raise-Large-Monoid l2 x ＝ raise-Large-Monoid l1 y))
  eq-raise-iff-sim-Large-Monoid =
    eq-raise-iff-sim-Large-Semigroup (large-semigroup-Large-Monoid M)

  eq-raise-sim-Large-Monoid' :
    {l1 l2 : Level}
    (x : type-Large-Monoid M (l1 ⊔ l2)) (y : type-Large-Monoid M l2) →
    sim-Large-Monoid M x y → x ＝ raise-Large-Monoid l1 y
  eq-raise-sim-Large-Monoid' =
    eq-raise-sim-Cumulative-Large-Set' (cumulative-large-set-Large-Monoid M)

  sim-raise-raise-Large-Monoid :
    {l0 : Level} (l1 l2 : Level) (x : type-Large-Monoid M l0) →
    sim-Large-Monoid M (raise-Large-Monoid l1 x) (raise-Large-Monoid l2 x)
  sim-raise-raise-Large-Monoid =
    sim-raise-raise-Large-Semigroup (large-semigroup-Large-Monoid M)
```

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

  sim-preserving-binary-operator-mul-Large-Monoid :
    sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Monoid M)
  sim-preserving-binary-operator-mul-Large-Monoid =
    sim-preserving-binary-operator-mul-Large-Semigroup
      ( large-semigroup-Large-Monoid M)

  preserves-sim-mul-Large-Monoid :
    preserves-sim-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Monoid M)
      ( mul-Large-Monoid M)
  preserves-sim-mul-Large-Monoid =
    preserves-sim-mul-Large-Semigroup (large-semigroup-Large-Monoid M)

  sim-preserving-map-left-mul-Large-Monoid :
    {l : Level} (x : type-Large-Monoid M l) →
    sim-preserving-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Monoid M)
  sim-preserving-map-left-mul-Large-Monoid =
    sim-preserving-map-left-mul-Large-Semigroup (large-semigroup-Large-Monoid M)

  preserves-sim-left-mul-Large-Monoid :
    {l : Level} (x : type-Large-Monoid M l) →
    preserves-sim-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Monoid M)
      ( mul-Large-Monoid M x)
  preserves-sim-left-mul-Large-Monoid =
    preserves-sim-left-mul-Large-Semigroup (large-semigroup-Large-Monoid M)

  sim-preserving-map-right-mul-Large-Monoid :
    {l : Level} (y : type-Large-Monoid M l) →
    sim-preserving-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Monoid M)
  sim-preserving-map-right-mul-Large-Monoid =
    sim-preserving-map-right-mul-Large-Semigroup
      ( large-semigroup-Large-Monoid M)

  preserves-sim-right-mul-Large-Monoid :
    {l : Level} (y : type-Large-Monoid M l) →
    preserves-sim-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Monoid M)
      ( mul-Large-Monoid' M y)
  preserves-sim-right-mul-Large-Monoid =
    preserves-sim-right-mul-Large-Semigroup (large-semigroup-Large-Monoid M)
```

### Floating raised universe levels out of multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  abstract
    mul-raise-right-Large-Monoid :
      {l1 l2 : Level} (l3 : Level) →
      (x : type-Large-Monoid M l1) (y : type-Large-Monoid M l2) →
      mul-Large-Monoid M x (raise-Large-Monoid M l3 y) ＝
      raise-Large-Monoid M l3 (mul-Large-Monoid M x y)
    mul-raise-right-Large-Monoid =
      mul-raise-right-Large-Semigroup (large-semigroup-Large-Monoid M)

    mul-raise-left-Large-Monoid :
      {l1 l2 : Level} (l3 : Level) →
      (x : type-Large-Monoid M l1) (y : type-Large-Monoid M l2) →
      mul-Large-Monoid M (raise-Large-Monoid M l3 x) y ＝
      raise-Large-Monoid M l3 (mul-Large-Monoid M x y)
    mul-raise-left-Large-Monoid =
      mul-raise-left-Large-Semigroup (large-semigroup-Large-Monoid M)

    mul-raise-raise-Large-Monoid :
      {l1 l2 : Level} (l3 l4 : Level) →
      (x : type-Large-Monoid M l1) (y : type-Large-Monoid M l2) →
      mul-Large-Monoid M
        ( raise-Large-Monoid M l3 x)
        ( raise-Large-Monoid M l4 y) ＝
      raise-Large-Monoid M (l3 ⊔ l4) (mul-Large-Monoid M x y)
    mul-raise-raise-Large-Monoid =
      mul-raise-raise-Large-Semigroup (large-semigroup-Large-Monoid M)
```

### Raised unit laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  raise-unit-Large-Monoid : (l : Level) → type-Large-Monoid M l
  raise-unit-Large-Monoid l =
    raise-Large-Monoid M l (unit-Large-Monoid M)

  abstract
    raise-unit-lzero-Large-Monoid :
      raise-unit-Large-Monoid lzero ＝ unit-Large-Monoid M
    raise-unit-lzero-Large-Monoid =
      eq-raise-Large-Monoid M (unit-Large-Monoid M)

    raise-left-unit-law-mul-Large-Monoid :
      {l1 l2 : Level} (x : type-Large-Monoid M l1) →
      mul-Large-Monoid M (raise-unit-Large-Monoid l2) x ＝
      raise-Large-Monoid M l2 x
    raise-left-unit-law-mul-Large-Monoid {l1} {l2} x =
      ( mul-raise-left-Large-Monoid M l2 (unit-Large-Monoid M) x) ∙
      ( ap (raise-Large-Monoid M l2) (left-unit-law-mul-Large-Monoid M x))

    raise-right-unit-law-mul-Large-Monoid :
      {l1 l2 : Level} (x : type-Large-Monoid M l1) →
      mul-Large-Monoid M x (raise-unit-Large-Monoid l2) ＝
      raise-Large-Monoid M l2 x
    raise-right-unit-law-mul-Large-Monoid {l1} {l2} x =
      ( mul-raise-right-Large-Monoid M l2 x (unit-Large-Monoid M)) ∙
      ( ap (raise-Large-Monoid M l2) (right-unit-law-mul-Large-Monoid M x))
```

### Unit elements in large monoids

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  is-unit-prop-Large-Monoid :
    {l : Level} → type-Large-Monoid M l → Prop (β l lzero)
  is-unit-prop-Large-Monoid x = sim-prop-Large-Monoid M x (unit-Large-Monoid M)

  is-unit-Large-Monoid :
    {l : Level} → type-Large-Monoid M l → UU (β l lzero)
  is-unit-Large-Monoid x = type-Prop (is-unit-prop-Large-Monoid x)

  is-unit-unit-Large-Monoid :
    is-unit-Large-Monoid (unit-Large-Monoid M)
  is-unit-unit-Large-Monoid =
    refl-sim-Large-Monoid M (unit-Large-Monoid M)

  is-unit-raise-unit-Large-Monoid :
    (l : Level) → is-unit-Large-Monoid (raise-unit-Large-Monoid M l)
  is-unit-raise-unit-Large-Monoid l =
    sim-raise-Large-Monoid' M l (unit-Large-Monoid M)

  abstract
    eq-raise-unit-is-unit-Large-Monoid :
      {l : Level} (x : type-Large-Monoid M l) →
      is-unit-Large-Monoid x → x ＝ raise-unit-Large-Monoid M l
    eq-raise-unit-is-unit-Large-Monoid {l} x =
      eq-raise-sim-Large-Monoid' M x (unit-Large-Monoid M)

module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  {l1 l2 : Level}
  (x : type-Large-Monoid M l1) (y : type-Large-Monoid M l2)
  where

  abstract
    eq-left-is-unit-law-mul-Large-Monoid :
      is-unit-Large-Monoid M x →
      mul-Large-Monoid M x y ＝ raise-Large-Monoid M l1 y
    eq-left-is-unit-law-mul-Large-Monoid x~1 =
      ( ap-mul-Large-Monoid M
        ( eq-raise-unit-is-unit-Large-Monoid M x x~1)
        ( refl)) ∙
      ( raise-left-unit-law-mul-Large-Monoid M y)

    eq-right-is-unit-law-mul-Large-Monoid :
      is-unit-Large-Monoid M y →
      mul-Large-Monoid M x y ＝ raise-Large-Monoid M l2 x
    eq-right-is-unit-law-mul-Large-Monoid y~1 =
      ( ap-mul-Large-Monoid M
        ( refl)
        ( eq-raise-unit-is-unit-Large-Monoid M y y~1)) ∙
      ( raise-right-unit-law-mul-Large-Monoid M x)

    sim-left-is-unit-law-mul-Large-Monoid :
      is-unit-Large-Monoid M x → sim-Large-Monoid M (mul-Large-Monoid M x y) y
    sim-left-is-unit-law-mul-Large-Monoid x~1 =
      inv-tr
        ( λ z → sim-Large-Monoid M z y)
        ( eq-left-is-unit-law-mul-Large-Monoid x~1)
        ( sim-raise-Large-Monoid' M l1 y)

    sim-right-is-unit-law-mul-Large-Monoid :
      is-unit-Large-Monoid M y → sim-Large-Monoid M (mul-Large-Monoid M x y) x
    sim-right-is-unit-law-mul-Large-Monoid y~1 =
      inv-tr
        ( λ z → sim-Large-Monoid M z x)
        ( eq-right-is-unit-law-mul-Large-Monoid y~1)
        ( sim-raise-Large-Monoid' M l2 x)
```

### Small monoids from large monoids

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  semigroup-Large-Monoid : (l : Level) → Semigroup (α l)
  semigroup-Large-Monoid =
    semigroup-Large-Semigroup (large-semigroup-Large-Monoid M)

  monoid-Large-Monoid : (l : Level) → Monoid (α l)
  monoid-Large-Monoid l =
    ( semigroup-Large-Monoid l ,
      raise-unit-Large-Monoid M l ,
      ( λ x →
        raise-left-unit-law-mul-Large-Monoid M x ∙ eq-raise-Large-Monoid M _) ,
      ( λ x →
        raise-right-unit-law-mul-Large-Monoid M x ∙ eq-raise-Large-Monoid M _))
```

### The raise operation is a monoid homomorphism

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  hom-raise-Large-Monoid :
    (l1 l2 : Level) →
    hom-Monoid
      ( monoid-Large-Monoid M l1)
      ( monoid-Large-Monoid M (l1 ⊔ l2))
  hom-raise-Large-Monoid l1 l2 =
    ( hom-raise-Large-Semigroup (large-semigroup-Large-Monoid M) l1 l2 ,
      raise-raise-Large-Monoid M l2 l1 (unit-Large-Monoid M))
```
