# Large semigroups

```agda
{-# OPTIONS --lossy-unification #-}

module group-theory.large-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.cumulative-large-sets
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.large-similarity-relations
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.similarity-preserving-binary-maps-cumulative-large-sets
open import foundation.similarity-preserving-maps-cumulative-large-sets
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups
open import group-theory.semigroups
```

</details>

## Idea

A {{#concept "large semigroup" Agda=Large-Semigroup}} consists of:

- A [cumulative large set](foundation.cumulative-large-sets.md) `X`
- A
  [similarity-preserving binary map](foundation.similarity-preserving-binary-maps-cumulative-large-sets.md)
  `μ : (l1 l2 : Level) → X l1 → X l2 → X (l1 ⊔ l2)` satisfying the following
  associativity law:

```text
  μ (l1 ⊔ l2) l3 (μ l1 l2 x y) z ＝ μ l1 (l2 ⊔ l3) x (μ l2 l3 y z).
```

## Definitions

```agda
record Large-Semigroup (α : Level → Level) (β : Level → Level → Level) : UUω
  where

  constructor
    make-Large-Semigroup
  field
    cumulative-large-set-Large-Semigroup :
      Cumulative-Large-Set α β
    sim-preserving-binary-operator-mul-Large-Semigroup :
      sim-preserving-binary-operator-Cumulative-Large-Set
        ( cumulative-large-set-Large-Semigroup)

  set-Large-Semigroup : (l : Level) → Set (α l)
  set-Large-Semigroup =
    set-Cumulative-Large-Set cumulative-large-set-Large-Semigroup

  type-Large-Semigroup : (l : Level) → UU (α l)
  type-Large-Semigroup l = type-Set (set-Large-Semigroup l)

  mul-Large-Semigroup :
    {l1 l2 : Level} →
    type-Large-Semigroup l1 →
    type-Large-Semigroup l2 →
    type-Large-Semigroup (l1 ⊔ l2)
  mul-Large-Semigroup =
    map-sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Semigroup)
      ( sim-preserving-binary-operator-mul-Large-Semigroup)

  mul-Large-Semigroup' :
    {l1 l2 : Level} →
    type-Large-Semigroup l1 →
    type-Large-Semigroup l2 →
    type-Large-Semigroup (l1 ⊔ l2)
  mul-Large-Semigroup' y x = mul-Large-Semigroup x y

  field
    associative-mul-Large-Semigroup :
      {l1 l2 l3 : Level}
      (x : type-Large-Semigroup l1)
      (y : type-Large-Semigroup l2)
      (z : type-Large-Semigroup l3) →
      mul-Large-Semigroup (mul-Large-Semigroup x y) z ＝
      mul-Large-Semigroup x (mul-Large-Semigroup y z)

open Large-Semigroup public
```

## Properties

### Similarity in large semigroups

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (G : Large-Semigroup α β)
  where

  large-similarity-relation-Large-Semigroup :
    Large-Similarity-Relation β (type-Large-Semigroup G)
  large-similarity-relation-Large-Semigroup =
    large-similarity-relation-Cumulative-Large-Set
      ( cumulative-large-set-Large-Semigroup G)

  sim-prop-Large-Semigroup : Large-Relation-Prop β (type-Large-Semigroup G)
  sim-prop-Large-Semigroup =
    sim-prop-Cumulative-Large-Set (cumulative-large-set-Large-Semigroup G)

  sim-Large-Semigroup : Large-Relation β (type-Large-Semigroup G)
  sim-Large-Semigroup =
    sim-Cumulative-Large-Set (cumulative-large-set-Large-Semigroup G)

  refl-sim-Large-Semigroup :
    is-reflexive-Large-Relation (type-Large-Semigroup G) sim-Large-Semigroup
  refl-sim-Large-Semigroup =
    refl-sim-Cumulative-Large-Set (cumulative-large-set-Large-Semigroup G)

  symmetric-sim-Large-Semigroup :
    is-symmetric-Large-Relation (type-Large-Semigroup G) sim-Large-Semigroup
  symmetric-sim-Large-Semigroup =
    symmetric-sim-Cumulative-Large-Set (cumulative-large-set-Large-Semigroup G)

  transitive-sim-Large-Semigroup :
    is-transitive-Large-Relation (type-Large-Semigroup G) sim-Large-Semigroup
  transitive-sim-Large-Semigroup =
    transitive-sim-Cumulative-Large-Set (cumulative-large-set-Large-Semigroup G)

  eq-sim-Large-Semigroup :
    {l : Level} (x y : type-Large-Semigroup G l) →
    sim-Large-Semigroup x y → x ＝ y
  eq-sim-Large-Semigroup =
    eq-sim-Cumulative-Large-Set (cumulative-large-set-Large-Semigroup G)

  sim-eq-Large-Semigroup :
    {l : Level} {x y : type-Large-Semigroup G l} →
    x ＝ y → sim-Large-Semigroup x y
  sim-eq-Large-Semigroup =
    sim-eq-Cumulative-Large-Set (cumulative-large-set-Large-Semigroup G)
```

### Raising universe levels in large semigroups

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (G : Large-Semigroup α β)
  where

  raise-Large-Semigroup :
    {l0 : Level} (l : Level) →
    type-Large-Semigroup G l0 → type-Large-Semigroup G (l ⊔ l0)
  raise-Large-Semigroup =
    raise-Cumulative-Large-Set (cumulative-large-set-Large-Semigroup G)

  sim-raise-Large-Semigroup :
    {l0 : Level} (l : Level) (x : type-Large-Semigroup G l0) →
    sim-Large-Semigroup G x (raise-Large-Semigroup l x)
  sim-raise-Large-Semigroup =
    sim-raise-Cumulative-Large-Set (cumulative-large-set-Large-Semigroup G)

  sim-raise-Large-Semigroup' :
    {l0 : Level} (l : Level) (x : type-Large-Semigroup G l0) →
    sim-Large-Semigroup G (raise-Large-Semigroup l x) x
  sim-raise-Large-Semigroup' =
    sim-raise-Cumulative-Large-Set' (cumulative-large-set-Large-Semigroup G)

  eq-raise-Large-Semigroup :
    {l : Level} (x : type-Large-Semigroup G l) →
    raise-Large-Semigroup l x ＝ x
  eq-raise-Large-Semigroup =
    eq-raise-Cumulative-Large-Set (cumulative-large-set-Large-Semigroup G)

  eq-raise-leq-level-Large-Semigroup :
    (l1 : Level) {l2 : Level} (x : type-Large-Semigroup G (l1 ⊔ l2)) →
    raise-Large-Semigroup l2 x ＝ x
  eq-raise-leq-level-Large-Semigroup =
    eq-raise-leq-level-Cumulative-Large-Set
      ( cumulative-large-set-Large-Semigroup G)

  is-emb-raise-Large-Semigroup :
    (l1 l2 : Level) → is-emb (raise-Large-Semigroup {l1} l2)
  is-emb-raise-Large-Semigroup =
    is-emb-raise-Cumulative-Large-Set (cumulative-large-set-Large-Semigroup G)

  emb-raise-Large-Semigroup :
    (l1 l2 : Level) →
    type-Large-Semigroup G l1 ↪ type-Large-Semigroup G (l1 ⊔ l2)
  emb-raise-Large-Semigroup =
    emb-raise-Cumulative-Large-Set (cumulative-large-set-Large-Semigroup G)

  eq-raise-sim-Large-Semigroup :
    {l1 l2 : Level} →
    (x : type-Large-Semigroup G l1) (y : type-Large-Semigroup G l2) →
    sim-Large-Semigroup G x y →
    raise-Large-Semigroup l2 x ＝ raise-Large-Semigroup l1 y
  eq-raise-sim-Large-Semigroup =
    eq-raise-sim-Cumulative-Large-Set (cumulative-large-set-Large-Semigroup G)

  sim-eq-raise-Large-Semigroup :
    {l1 l2 : Level} →
    (x : type-Large-Semigroup G l1) (y : type-Large-Semigroup G l2) →
    raise-Large-Semigroup l2 x ＝ raise-Large-Semigroup l1 y →
    sim-Large-Semigroup G x y
  sim-eq-raise-Large-Semigroup =
    sim-eq-raise-Cumulative-Large-Set (cumulative-large-set-Large-Semigroup G)

  eq-raise-iff-sim-Large-Semigroup :
    {l1 l2 : Level} →
    (x : type-Large-Semigroup G l1) (y : type-Large-Semigroup G l2) →
    ( sim-Large-Semigroup G x y ↔
      ( raise-Large-Semigroup l2 x ＝ raise-Large-Semigroup l1 y))
  eq-raise-iff-sim-Large-Semigroup =
    eq-raise-iff-sim-Cumulative-Large-Set
      ( cumulative-large-set-Large-Semigroup G)

  sim-raise-raise-Large-Semigroup :
    {l0 : Level} (l1 l2 : Level) (x : type-Large-Semigroup G l0) →
    sim-Large-Semigroup G
      ( raise-Large-Semigroup l1 x)
      ( raise-Large-Semigroup l2 x)
  sim-raise-raise-Large-Semigroup =
    sim-raise-raise-Cumulative-Large-Set
      ( cumulative-large-set-Large-Semigroup G)

  raise-raise-Large-Semigroup :
    {l0 l1 l2 : Level} (x : type-Large-Semigroup G l0) →
    raise-Large-Semigroup l1 (raise-Large-Semigroup l2 x) ＝
    raise-Large-Semigroup (l1 ⊔ l2) x
  raise-raise-Large-Semigroup =
    raise-raise-Cumulative-Large-Set (cumulative-large-set-Large-Semigroup G)

  eq-raise-sim-Large-Semigroup' :
    {l1 l2 : Level}
    (x : type-Large-Semigroup G (l1 ⊔ l2)) (y : type-Large-Semigroup G l2) →
    sim-Large-Semigroup G x y → x ＝ raise-Large-Semigroup l1 y
  eq-raise-sim-Large-Semigroup' =
    eq-raise-sim-Cumulative-Large-Set' (cumulative-large-set-Large-Semigroup G)
```

### Multiplication in large semigroups

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (G : Large-Semigroup α β)
  where

  preserves-sim-mul-Large-Semigroup :
    preserves-sim-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Semigroup G)
      ( mul-Large-Semigroup G)
  preserves-sim-mul-Large-Semigroup =
    preserves-sim-map-sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Semigroup G)
      ( sim-preserving-binary-operator-mul-Large-Semigroup G)

  sim-preserving-map-left-mul-Large-Semigroup :
    {l : Level} (x : type-Large-Semigroup G l) →
    sim-preserving-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Semigroup G)
  sim-preserving-map-left-mul-Large-Semigroup =
    sim-preserving-endomap-ev-right-sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Semigroup G)
      ( sim-preserving-binary-operator-mul-Large-Semigroup G)

  sim-preserving-map-right-mul-Large-Semigroup :
    {l : Level} (y : type-Large-Semigroup G l) →
    sim-preserving-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Semigroup G)
  sim-preserving-map-right-mul-Large-Semigroup =
    sim-preserving-endomap-ev-left-sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Semigroup G)
      ( sim-preserving-binary-operator-mul-Large-Semigroup G)

  preserves-sim-left-mul-Large-Semigroup :
    {l : Level} (x : type-Large-Semigroup G l) →
    preserves-sim-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Semigroup G)
      ( mul-Large-Semigroup G x)
  preserves-sim-left-mul-Large-Semigroup x =
    preserves-sim-map-sim-preserving-endomap-Cumulative-Large-Set
      ( cumulative-large-set-Large-Semigroup G)
      ( sim-preserving-map-left-mul-Large-Semigroup x)

  preserves-sim-right-mul-Large-Semigroup :
    {l : Level} (y : type-Large-Semigroup G l) →
    preserves-sim-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Semigroup G)
      ( mul-Large-Semigroup' G y)
  preserves-sim-right-mul-Large-Semigroup y =
    preserves-sim-map-sim-preserving-endomap-Cumulative-Large-Set
      ( cumulative-large-set-Large-Semigroup G)
      ( sim-preserving-map-right-mul-Large-Semigroup y)

  mul-raise-left-Large-Semigroup :
    {l1 l2 : Level} (l3 : Level) →
    (x : type-Large-Semigroup G l1) (y : type-Large-Semigroup G l2) →
    mul-Large-Semigroup G (raise-Large-Semigroup G l3 x) y ＝
    raise-Large-Semigroup G l3 (mul-Large-Semigroup G x y)
  mul-raise-left-Large-Semigroup =
    map-raise-left-sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Semigroup G)
      ( sim-preserving-binary-operator-mul-Large-Semigroup G)

  mul-raise-right-Large-Semigroup :
    {l1 l2 : Level} (l3 : Level) →
    (x : type-Large-Semigroup G l1) (y : type-Large-Semigroup G l2) →
    mul-Large-Semigroup G x (raise-Large-Semigroup G l3 y) ＝
    raise-Large-Semigroup G l3 (mul-Large-Semigroup G x y)
  mul-raise-right-Large-Semigroup =
    map-raise-right-sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Semigroup G)
      ( sim-preserving-binary-operator-mul-Large-Semigroup G)

  mul-raise-raise-Large-Semigroup :
    {l1 l2 : Level} (l3 : Level) (l4 : Level) →
    (x : type-Large-Semigroup G l1) (y : type-Large-Semigroup G l2) →
    mul-Large-Semigroup G
      ( raise-Large-Semigroup G l3 x)
      ( raise-Large-Semigroup G l4 y) ＝
    raise-Large-Semigroup G (l3 ⊔ l4) (mul-Large-Semigroup G x y)
  mul-raise-raise-Large-Semigroup =
    map-raise-raise-sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Semigroup G)
      ( sim-preserving-binary-operator-mul-Large-Semigroup G)
```

### Small semigroups from large semigroups

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (G : Large-Semigroup α β)
  where

  semigroup-Large-Semigroup : (l : Level) → Semigroup (α l)
  pr1 (semigroup-Large-Semigroup l) = set-Large-Semigroup G l
  pr1 (pr2 (semigroup-Large-Semigroup l)) = mul-Large-Semigroup G
  pr2 (pr2 (semigroup-Large-Semigroup l)) = associative-mul-Large-Semigroup G
```

### The raise operation is a semigroup homomorphism between small semigroups

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (G : Large-Semigroup α β)
  where

  hom-raise-Large-Semigroup :
    (l1 l2 : Level) →
    hom-Semigroup
      ( semigroup-Large-Semigroup G l1)
      ( semigroup-Large-Semigroup G (l1 ⊔ l2))
  hom-raise-Large-Semigroup l1 l2 =
    ( raise-Large-Semigroup G l2 ,
      λ {x} {y} → inv (mul-raise-raise-Large-Semigroup G l2 l2 x y))
```
