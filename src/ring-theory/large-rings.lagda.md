# Large rings

```agda
module ring-theory.large-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cumulative-large-sets
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.function-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.large-similarity-relations
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.similarity-preserving-binary-maps-cumulative-large-sets
open import foundation.similarity-preserving-maps-cumulative-large-sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.difference-large-abelian-groups
open import group-theory.large-abelian-groups
open import group-theory.large-monoids
open import group-theory.large-semigroups
open import group-theory.monoids

open import ring-theory.homomorphisms-rings
open import ring-theory.rings
```

</details>

## Idea

A {{#concept "large ring" Agda=Large-Ring}} is a
[large abelian group](group-theory.large-abelian-groups.md) endowed with an
additional operation, called multiplication, which in addition to forming a
[large monoid](group-theory.large-monoids.md) is distributive over addition.

## Definition

```agda
record Large-Ring (α : Level → Level) (β : Level → Level → Level) : UUω where

  constructor
    make-Large-Ring

  field
    large-ab-Large-Ring : Large-Ab α β

  cumulative-large-set-Large-Ring : Cumulative-Large-Set α β
  cumulative-large-set-Large-Ring =
    cumulative-large-set-Large-Ab large-ab-Large-Ring

  type-Large-Ring : (l : Level) → UU (α l)
  type-Large-Ring = type-Large-Ab large-ab-Large-Ring

  set-Large-Ring : (l : Level) → Set (α l)
  set-Large-Ring = set-Large-Ab large-ab-Large-Ring

  add-Large-Ring :
    {l1 l2 : Level} →
    type-Large-Ring l1 → type-Large-Ring l2 → type-Large-Ring (l1 ⊔ l2)
  add-Large-Ring = add-Large-Ab large-ab-Large-Ring

  add-Large-Ring' :
    {l1 l2 : Level} →
    type-Large-Ring l1 → type-Large-Ring l2 → type-Large-Ring (l1 ⊔ l2)
  add-Large-Ring' x y = add-Large-Ring y x

  neg-Large-Ring : {l : Level} → type-Large-Ring l → type-Large-Ring l
  neg-Large-Ring = neg-Large-Ab large-ab-Large-Ring

  diff-Large-Ring :
    {l1 l2 : Level} →
    type-Large-Ring l1 → type-Large-Ring l2 → type-Large-Ring (l1 ⊔ l2)
  diff-Large-Ring = right-diff-Large-Ab large-ab-Large-Ring

  field
    sim-preserving-binary-operator-mul-Large-Ring :
      sim-preserving-binary-operator-Cumulative-Large-Set
        ( cumulative-large-set-Large-Ring)

  mul-Large-Ring :
    {l1 l2 : Level} →
    type-Large-Ring l1 → type-Large-Ring l2 → type-Large-Ring (l1 ⊔ l2)
  mul-Large-Ring =
    map-sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Ring)
      ( sim-preserving-binary-operator-mul-Large-Ring)

  field
    one-Large-Ring : type-Large-Ring lzero

    associative-mul-Large-Ring :
      {l1 l2 l3 : Level} →
      (a : type-Large-Ring l1) →
      (b : type-Large-Ring l2) →
      (c : type-Large-Ring l3) →
      mul-Large-Ring (mul-Large-Ring a b) c ＝
      mul-Large-Ring a (mul-Large-Ring b c)

    sim-left-unit-law-mul-Large-Ring :
      {l : Level} (a : type-Large-Ring l) → mul-Large-Ring one-Large-Ring a ＝ a

    sim-right-unit-law-mul-Large-Ring :
      {l : Level} (a : type-Large-Ring l) → mul-Large-Ring a one-Large-Ring ＝ a

    left-distributive-mul-add-Large-Ring :
      {l1 l2 l3 : Level} →
      (a : type-Large-Ring l1) →
      (b : type-Large-Ring l2) →
      (c : type-Large-Ring l3) →
      mul-Large-Ring a (add-Large-Ring b c) ＝
      add-Large-Ring (mul-Large-Ring a b) (mul-Large-Ring a c)

    right-distributive-mul-add-Large-Ring :
      {l1 l2 l3 : Level} →
      (a : type-Large-Ring l1) →
      (b : type-Large-Ring l2) →
      (c : type-Large-Ring l3) →
      mul-Large-Ring (add-Large-Ring a b) c ＝
      add-Large-Ring (mul-Large-Ring a c) (mul-Large-Ring b c)

  ap-add-Large-Ring :
    {l1 l2 : Level}
    {x x' : type-Large-Ring l1} → x ＝ x' →
    {y y' : type-Large-Ring l2} → y ＝ y' →
    add-Large-Ring x y ＝ add-Large-Ring x' y'
  ap-add-Large-Ring = ap-binary add-Large-Ring

  ap-mul-Large-Ring :
    {l1 l2 : Level}
    {x x' : type-Large-Ring l1} → x ＝ x' →
    {y y' : type-Large-Ring l2} → y ＝ y' →
    mul-Large-Ring x y ＝ mul-Large-Ring x' y'
  ap-mul-Large-Ring = ap-binary mul-Large-Ring

open Large-Ring public
```

## Properties

### Similarity

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (R : Large-Ring α β)
  where

  large-similarity-relation-Large-Ring :
    Large-Similarity-Relation β (type-Large-Ring R)
  large-similarity-relation-Large-Ring =
    large-similarity-relation-Large-Ab (large-ab-Large-Ring R)

  sim-prop-Large-Ring :
    Large-Relation-Prop β (type-Large-Ring R)
  sim-prop-Large-Ring =
    sim-prop-Large-Ab (large-ab-Large-Ring R)

  sim-Large-Ring : Large-Relation β (type-Large-Ring R)
  sim-Large-Ring = sim-Large-Ab (large-ab-Large-Ring R)

  refl-sim-Large-Ring :
    is-reflexive-Large-Relation (type-Large-Ring R) sim-Large-Ring
  refl-sim-Large-Ring =
    refl-sim-Large-Ab (large-ab-Large-Ring R)

  symmetric-sim-Large-Ring :
    is-symmetric-Large-Relation (type-Large-Ring R) sim-Large-Ring
  symmetric-sim-Large-Ring =
    symmetric-sim-Large-Ab (large-ab-Large-Ring R)

  transitive-sim-Large-Ring :
    is-transitive-Large-Relation (type-Large-Ring R) sim-Large-Ring
  transitive-sim-Large-Ring =
    transitive-sim-Large-Ab (large-ab-Large-Ring R)

  sim-eq-Large-Ring :
    {l : Level} {x y : type-Large-Ring R l} → x ＝ y → sim-Large-Ring x y
  sim-eq-Large-Ring = sim-eq-Large-Ab (large-ab-Large-Ring R)

  eq-sim-Large-Ring :
    {l : Level} (x y : type-Large-Ring R l) → sim-Large-Ring x y → x ＝ y
  eq-sim-Large-Ring = eq-sim-Large-Ab (large-ab-Large-Ring R)
```

### Similarity reasoning on large abelian groups

```agda
module
  similarity-reasoning-Large-Ring
    {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  open similarity-reasoning-Large-Ab (large-ab-Large-Ring R) public
```

### Raising universe levels

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (R : Large-Ring α β)
  where

  raise-Large-Ring :
    {l0 : Level} (l : Level) →
    type-Large-Ring R l0 → type-Large-Ring R (l0 ⊔ l)
  raise-Large-Ring = raise-Large-Ab (large-ab-Large-Ring R)

  sim-raise-Large-Ring :
    {l0 : Level} (l : Level) (x : type-Large-Ring R l0) →
    sim-Large-Ring R x (raise-Large-Ring l x)
  sim-raise-Large-Ring =
    sim-raise-Large-Ab (large-ab-Large-Ring R)

  sim-raise-Large-Ring' :
    {l0 : Level} (l : Level) (x : type-Large-Ring R l0) →
    sim-Large-Ring R (raise-Large-Ring l x) x
  sim-raise-Large-Ring' =
    sim-raise-Large-Ab' (large-ab-Large-Ring R)

  eq-raise-Large-Ring :
    {l : Level} (x : type-Large-Ring R l) → raise-Large-Ring l x ＝ x
  eq-raise-Large-Ring =
    eq-raise-Large-Ab (large-ab-Large-Ring R)

  is-emb-raise-Large-Ring :
    (l1 l2 : Level) → is-emb (raise-Large-Ring {l1} l2)
  is-emb-raise-Large-Ring =
    is-emb-raise-Large-Ab (large-ab-Large-Ring R)

  emb-raise-Large-Ring :
    (l1 l2 : Level) → type-Large-Ring R l1 ↪ type-Large-Ring R (l1 ⊔ l2)
  emb-raise-Large-Ring =
    emb-raise-Large-Ab (large-ab-Large-Ring R)

  raise-raise-Large-Ring :
    {l0 l1 l2 : Level} (x : type-Large-Ring R l0) →
    raise-Large-Ring l1 (raise-Large-Ring l2 x) ＝
    raise-Large-Ring (l1 ⊔ l2) x
  raise-raise-Large-Ring =
    raise-raise-Large-Ab (large-ab-Large-Ring R)

  eq-raise-sim-Large-Ring :
    {l1 l2 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
    sim-Large-Ring R x y → raise-Large-Ring l2 x ＝ raise-Large-Ring l1 y
  eq-raise-sim-Large-Ring =
    eq-raise-sim-Large-Ab (large-ab-Large-Ring R)

  sim-eq-raise-Large-Ring :
    {l1 l2 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
    raise-Large-Ring l2 x ＝ raise-Large-Ring l1 y → sim-Large-Ring R x y
  sim-eq-raise-Large-Ring =
    sim-eq-raise-Large-Ab (large-ab-Large-Ring R)

  eq-raise-iff-sim-Large-Ring :
    {l1 l2 : Level} →
    (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
    ( sim-Large-Ring R x y ↔
      ( raise-Large-Ring l2 x ＝ raise-Large-Ring l1 y))
  eq-raise-iff-sim-Large-Ring =
    eq-raise-iff-sim-Large-Ab (large-ab-Large-Ring R)

  eq-raise-sim-Large-Ring' :
    {l1 l2 : Level}
    (x : type-Large-Ring R (l1 ⊔ l2)) (y : type-Large-Ring R l2) →
    sim-Large-Ring R x y → x ＝ raise-Large-Ring l1 y
  eq-raise-sim-Large-Ring' =
    eq-raise-sim-Large-Ab' (large-ab-Large-Ring R)
```

### Similarity preservation of addition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  sim-preserving-binary-operator-add-Large-Ring :
    sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Ring R)
  sim-preserving-binary-operator-add-Large-Ring =
    sim-preserving-binary-operator-add-Large-Ab (large-ab-Large-Ring R)

  preserves-sim-add-Large-Ring :
    preserves-sim-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Ring R)
      ( add-Large-Ring R)
  preserves-sim-add-Large-Ring =
    preserves-sim-add-Large-Ab (large-ab-Large-Ring R)

  sim-preserving-map-left-add-Large-Ring :
    {l : Level} (x : type-Large-Ring R l) →
    sim-preserving-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Ring R)
  sim-preserving-map-left-add-Large-Ring =
    sim-preserving-map-left-add-Large-Ab (large-ab-Large-Ring R)

  preserves-sim-left-add-Large-Ring :
    {l : Level} (x : type-Large-Ring R l) →
    preserves-sim-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Ring R)
      ( add-Large-Ring R x)
  preserves-sim-left-add-Large-Ring =
    preserves-sim-left-add-Large-Ab (large-ab-Large-Ring R)

  sim-preserving-map-right-add-Large-Ring :
    {l : Level} (y : type-Large-Ring R l) →
    sim-preserving-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Ring R)
  sim-preserving-map-right-add-Large-Ring =
    sim-preserving-map-right-add-Large-Ab
      ( large-ab-Large-Ring R)

  preserves-sim-right-add-Large-Ring :
    {l : Level} (y : type-Large-Ring R l) →
    preserves-sim-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Ring R)
      ( add-Large-Ring' R y)
  preserves-sim-right-add-Large-Ring =
    preserves-sim-right-add-Large-Ab (large-ab-Large-Ring R)
```

### Raising universe levels in multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  abstract
    add-raise-right-Large-Ring :
      {l1 l2 : Level} (l3 : Level) →
      (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
      add-Large-Ring R x (raise-Large-Ring R l3 y) ＝
      raise-Large-Ring R l3 (add-Large-Ring R x y)
    add-raise-right-Large-Ring =
      add-raise-right-Large-Ab (large-ab-Large-Ring R)

    add-raise-left-Large-Ring :
      {l1 l2 : Level} (l3 : Level) →
      (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
      add-Large-Ring R (raise-Large-Ring R l3 x) y ＝
      raise-Large-Ring R l3 (add-Large-Ring R x y)
    add-raise-left-Large-Ring =
      add-raise-left-Large-Ab (large-ab-Large-Ring R)

    add-raise-raise-Large-Ring :
      {l1 l2 : Level} (l3 l4 : Level) →
      (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
      add-Large-Ring R
        ( raise-Large-Ring R l3 x)
        ( raise-Large-Ring R l4 y) ＝
      raise-Large-Ring R (l3 ⊔ l4) (add-Large-Ring R x y)
    add-raise-raise-Large-Ring =
      add-raise-raise-Large-Ab (large-ab-Large-Ring R)
```

### The negation operation preserves similarity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  sim-preserving-endomap-neg-Large-Ring :
    sim-preserving-endomap-Cumulative-Large-Set
      ( id)
      ( cumulative-large-set-Large-Ring R)
  sim-preserving-endomap-neg-Large-Ring =
    sim-preserving-endomap-neg-Large-Ab (large-ab-Large-Ring R)

  preserves-sim-neg-Large-Ring :
    preserves-sim-endomap-Cumulative-Large-Set
      ( id)
      ( cumulative-large-set-Large-Ring R)
      ( neg-Large-Ring R)
  preserves-sim-neg-Large-Ring =
    preserves-sim-neg-Large-Ab (large-ab-Large-Ring R)
```

### Semigroup laws of addition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  associative-add-Large-Ring :
    {l1 l2 l3 : Level}
    (x : type-Large-Ring R l1)
    (y : type-Large-Ring R l2)
    (z : type-Large-Ring R l3) →
    add-Large-Ring R (add-Large-Ring R x y) z ＝
    add-Large-Ring R x (add-Large-Ring R y z)
  associative-add-Large-Ring =
    associative-add-Large-Ab (large-ab-Large-Ring R)
```

### Monoid laws of addition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  zero-Large-Ring : type-Large-Ring R lzero
  zero-Large-Ring = zero-Large-Ab (large-ab-Large-Ring R)

  raise-zero-Large-Ring : (l : Level) → type-Large-Ring R l
  raise-zero-Large-Ring = raise-zero-Large-Ab (large-ab-Large-Ring R)

  is-zero-prop-Large-Ring : {l : Level} → type-Large-Ring R l → Prop (β l lzero)
  is-zero-prop-Large-Ring = is-zero-prop-Large-Ab (large-ab-Large-Ring R)

  is-zero-Large-Ring : {l : Level} → type-Large-Ring R l → UU (β l lzero)
  is-zero-Large-Ring x = type-Prop (is-zero-prop-Large-Ring x)

  is-zero-zero-Large-Ring : is-zero-Large-Ring zero-Large-Ring
  is-zero-zero-Large-Ring =
    is-zero-zero-Large-Ab (large-ab-Large-Ring R)

  is-zero-raise-zero-Large-Ring :
    (l : Level) → is-zero-Large-Ring (raise-zero-Large-Ring l)
  is-zero-raise-zero-Large-Ring =
    is-zero-raise-zero-Large-Ab (large-ab-Large-Ring R)

  eq-raise-zero-is-zero-Large-Ring :
    {l : Level} (x : type-Large-Ring R l) →
    is-zero-Large-Ring x → x ＝ raise-zero-Large-Ring l
  eq-raise-zero-is-zero-Large-Ring =
    eq-raise-zero-is-zero-Large-Ab (large-ab-Large-Ring R)

  left-unit-law-add-Large-Ring :
    {l : Level} (x : type-Large-Ring R l) →
    add-Large-Ring R zero-Large-Ring x ＝ x
  left-unit-law-add-Large-Ring =
    left-unit-law-add-Large-Ab (large-ab-Large-Ring R)

  right-unit-law-add-Large-Ring :
    {l : Level} (x : type-Large-Ring R l) →
    add-Large-Ring R x zero-Large-Ring ＝ x
  right-unit-law-add-Large-Ring =
    right-unit-law-add-Large-Ab (large-ab-Large-Ring R)

  left-raise-unit-law-add-Large-Ring :
    {l1 l2 : Level} (y : type-Large-Ring R l2) →
    add-Large-Ring R (raise-zero-Large-Ring l1) y ＝ raise-Large-Ring R l1 y
  left-raise-unit-law-add-Large-Ring =
    left-raise-unit-law-add-Large-Ab (large-ab-Large-Ring R)

  right-raise-unit-law-add-Large-Ring :
    {l1 l2 : Level} (x : type-Large-Ring R l1) →
    add-Large-Ring R x (raise-zero-Large-Ring l2) ＝ raise-Large-Ring R l2 x
  right-raise-unit-law-add-Large-Ring =
    right-raise-unit-law-add-Large-Ab (large-ab-Large-Ring R)

  eq-left-is-zero-law-add-Large-Ring :
    {l1 l2 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
    is-zero-Large-Ring x → add-Large-Ring R x y ＝ raise-Large-Ring R l1 y
  eq-left-is-zero-law-add-Large-Ring =
    eq-left-is-zero-law-add-Large-Ab (large-ab-Large-Ring R)

  eq-right-is-zero-law-add-Large-Ring :
    {l1 l2 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
    is-zero-Large-Ring y → add-Large-Ring R x y ＝ raise-Large-Ring R l2 x
  eq-right-is-zero-law-add-Large-Ring =
    eq-right-is-zero-law-add-Large-Ab (large-ab-Large-Ring R)

  sim-left-is-zero-law-add-Large-Ring :
    {l1 l2 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
    is-zero-Large-Ring x → sim-Large-Ring R (add-Large-Ring R x y) y
  sim-left-is-zero-law-add-Large-Ring =
    sim-left-is-zero-law-add-Large-Ab (large-ab-Large-Ring R)

  sim-right-is-zero-law-add-Large-Ring :
    {l1 l2 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
    is-zero-Large-Ring y → sim-Large-Ring R (add-Large-Ring R x y) x
  sim-right-is-zero-law-add-Large-Ring =
    sim-right-is-zero-law-add-Large-Ab (large-ab-Large-Ring R)
```

### Group laws of addition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  abstract
    sim-left-inverse-law-add-Large-Ring :
      {l : Level} (x : type-Large-Ring R l) →
      is-zero-Large-Ring R (add-Large-Ring R (neg-Large-Ring R x) x)
    sim-left-inverse-law-add-Large-Ring =
      sim-left-inverse-law-add-Large-Ab (large-ab-Large-Ring R)

    sim-right-inverse-law-add-Large-Ring :
      {l : Level} (x : type-Large-Ring R l) →
      is-zero-Large-Ring R (add-Large-Ring R x (neg-Large-Ring R x))
    sim-right-inverse-law-add-Large-Ring =
      sim-right-inverse-law-add-Large-Ab (large-ab-Large-Ring R)

    eq-left-inverse-law-add-Large-Ring :
      {l : Level} (x : type-Large-Ring R l) →
      add-Large-Ring R (neg-Large-Ring R x) x ＝ raise-zero-Large-Ring R l
    eq-left-inverse-law-add-Large-Ring =
      eq-left-inverse-law-add-Large-Ab (large-ab-Large-Ring R)

    eq-right-inverse-law-add-Large-Ring :
      {l : Level} (x : type-Large-Ring R l) →
      add-Large-Ring R x (neg-Large-Ring R x) ＝ raise-zero-Large-Ring R l
    eq-right-inverse-law-add-Large-Ring =
      eq-right-inverse-law-add-Large-Ab (large-ab-Large-Ring R)
```

### Cancellation laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  {l1 l2 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2)
  where

  abstract
    sim-cancel-left-diff-add-Large-Ring :
      sim-Large-Ring R
        ( add-Large-Ring R (neg-Large-Ring R x) (add-Large-Ring R x y))
        ( y)
    sim-cancel-left-diff-add-Large-Ring =
      sim-cancel-left-diff-add-Large-Ab (large-ab-Large-Ring R) x y

    sim-cancel-left-add-diff-Large-Ring :
      sim-Large-Ring R
        ( add-Large-Ring R x (add-Large-Ring R (neg-Large-Ring R x) y))
        ( y)
    sim-cancel-left-add-diff-Large-Ring =
      sim-cancel-left-add-diff-Large-Ab (large-ab-Large-Ring R) x y

    sim-cancel-right-diff-add-Large-Ring :
      sim-Large-Ring R
        ( add-Large-Ring R (add-Large-Ring R y (neg-Large-Ring R x)) x)
        ( y)
    sim-cancel-right-diff-add-Large-Ring =
      sim-cancel-right-diff-add-Large-Ab (large-ab-Large-Ring R) x y

    sim-cancel-right-add-diff-Large-Ring :
      sim-Large-Ring R
        ( add-Large-Ring R (add-Large-Ring R y x) (neg-Large-Ring R x))
        ( y)
    sim-cancel-right-add-diff-Large-Ring =
      sim-cancel-right-add-diff-Large-Ab (large-ab-Large-Ring R) x y

    eq-cancel-left-diff-add-Large-Ring :
      add-Large-Ring R (neg-Large-Ring R x) (add-Large-Ring R x y) ＝
      raise-Large-Ring R l1 y
    eq-cancel-left-diff-add-Large-Ring =
      eq-cancel-left-diff-add-Large-Ab (large-ab-Large-Ring R) x y

    eq-cancel-left-add-diff-Large-Ring :
      add-Large-Ring R x (add-Large-Ring R (neg-Large-Ring R x) y) ＝
      raise-Large-Ring R l1 y
    eq-cancel-left-add-diff-Large-Ring =
      eq-cancel-left-add-diff-Large-Ab (large-ab-Large-Ring R) x y

    eq-cancel-right-diff-add-Large-Ring :
      add-Large-Ring R (add-Large-Ring R y (neg-Large-Ring R x)) x ＝
      raise-Large-Ring R l1 y
    eq-cancel-right-diff-add-Large-Ring =
      eq-cancel-right-diff-add-Large-Ab (large-ab-Large-Ring R) x y

    eq-cancel-right-add-diff-Large-Ring :
      add-Large-Ring R (add-Large-Ring R y x) (neg-Large-Ring R x) ＝
      raise-Large-Ring R l1 y
    eq-cancel-right-add-diff-Large-Ring =
      eq-cancel-right-add-diff-Large-Ab (large-ab-Large-Ring R) x y
```

### Uniqueness of negations

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  abstract
    unique-left-neg-Large-Ring :
      {l1 l2 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
      is-zero-Large-Ring R (add-Large-Ring R x y) →
      sim-Large-Ring R x (neg-Large-Ring R y)
    unique-left-neg-Large-Ring =
      unique-left-neg-Large-Ab (large-ab-Large-Ring R)

    unique-right-neg-Large-Ring :
      {l1 l2 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
      is-zero-Large-Ring R (add-Large-Ring R x y) →
      sim-Large-Ring R y (neg-Large-Ring R x)
    unique-right-neg-Large-Ring =
      unique-right-neg-Large-Ab (large-ab-Large-Ring R)
```

### The negation of zero is zero

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  abstract
    neg-is-zero-Large-Ring :
      {l : Level} (x : type-Large-Ring R l) →
      is-zero-Large-Ring R x → is-zero-Large-Ring R (neg-Large-Ring R x)
    neg-is-zero-Large-Ring = neg-is-zero-Large-Ab (large-ab-Large-Ring R)

    neg-zero-Large-Ring :
      neg-Large-Ring R (zero-Large-Ring R) ＝ zero-Large-Ring R
    neg-zero-Large-Ring = neg-zero-Large-Ab (large-ab-Large-Ring R)

    neg-raise-zero-Large-Ring :
      (l : Level) →
      neg-Large-Ring R (raise-zero-Large-Ring R l) ＝ raise-zero-Large-Ring R l
    neg-raise-zero-Large-Ring =
      neg-raise-zero-Large-Ab (large-ab-Large-Ring R)
```

### Distributivity of negation over addition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  abstract
    distributive-neg-add-Large-Ring :
      {l1 l2 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
      neg-Large-Ring R (add-Large-Ring R x y) ＝
      add-Large-Ring R (neg-Large-Ring R x) (neg-Large-Ring R y)
    distributive-neg-add-Large-Ring x y =
      distributive-neg-add-Large-Ab (large-ab-Large-Ring R) x y
```

### Negation is an involution

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  abstract
    neg-neg-Large-Ring :
      {l : Level} (x : type-Large-Ring R l) →
      neg-Large-Ring R (neg-Large-Ring R x) ＝ x
    neg-neg-Large-Ring = neg-neg-Large-Ab (large-ab-Large-Ring R)
```

### Addition reflects similarity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  {l1 l2 l3 : Level}
  (z : type-Large-Ring R l3)
  (x : type-Large-Ring R l1)
  (y : type-Large-Ring R l2)
  where

  abstract
    reflects-sim-right-add-Large-Ring :
      sim-Large-Ring R (add-Large-Ring R x z) (add-Large-Ring R y z) →
      sim-Large-Ring R x y
    reflects-sim-right-add-Large-Ring =
      reflects-sim-right-add-Large-Ab (large-ab-Large-Ring R) z x y

    reflects-sim-left-add-Large-Ring :
      sim-Large-Ring R (add-Large-Ring R z x) (add-Large-Ring R z y) →
      sim-Large-Ring R x y
    reflects-sim-left-add-Large-Ring =
      reflects-sim-left-add-Large-Ab (large-ab-Large-Ring R) z x y
```

### Left addition in a large abelian group is an embedding

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  {l1 : Level} (l2 : Level) (x : type-Large-Ring R l1)
  where

  abstract
    is-emb-left-add-Large-Ring :
      is-emb (add-Large-Ring R {l2 = l2} x)
    is-emb-left-add-Large-Ring =
      is-emb-left-add-Large-Ab (large-ab-Large-Ring R) l2 x
```

### Right addition in a large abelian group is an embedding

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  {l1 : Level} (l2 : Level) (x : type-Large-Ring R l1)
  where

  abstract
    is-emb-right-add-Large-Ring :
      is-emb (add-Large-Ring' R {l2 = l2} x)
    is-emb-right-add-Large-Ring =
      is-emb-right-add-Large-Ab (large-ab-Large-Ring R) l2 x
```

### The large monoid of multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  large-semigroup-mul-Large-Ring : Large-Semigroup α β
  large-semigroup-mul-Large-Ring =
    λ where
      .cumulative-large-set-Large-Semigroup →
        cumulative-large-set-Large-Ring R
      .sim-preserving-binary-operator-mul-Large-Semigroup →
        sim-preserving-binary-operator-mul-Large-Ring R
      .associative-mul-Large-Semigroup →
        associative-mul-Large-Ring R

  large-monoid-mul-Large-Ring : Large-Monoid α β
  large-monoid-mul-Large-Ring =
    λ where
      .large-semigroup-Large-Monoid →
        large-semigroup-mul-Large-Ring
      .unit-Large-Monoid →
        one-Large-Ring R
      .left-unit-law-mul-Large-Monoid →
        sim-left-unit-law-mul-Large-Ring R
      .right-unit-law-mul-Large-Monoid →
        sim-right-unit-law-mul-Large-Ring R
```

### Floating raised universe levels out of multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Ring α β)
  where

  abstract
    mul-raise-right-Large-Ring :
      {l1 l2 : Level} (l3 : Level) →
      (x : type-Large-Ring M l1) (y : type-Large-Ring M l2) →
      mul-Large-Ring M x (raise-Large-Ring M l3 y) ＝
      raise-Large-Ring M l3 (mul-Large-Ring M x y)
    mul-raise-right-Large-Ring =
      mul-raise-right-Large-Monoid (large-monoid-mul-Large-Ring M)

    mul-raise-left-Large-Ring :
      {l1 l2 : Level} (l3 : Level) →
      (x : type-Large-Ring M l1) (y : type-Large-Ring M l2) →
      mul-Large-Ring M (raise-Large-Ring M l3 x) y ＝
      raise-Large-Ring M l3 (mul-Large-Ring M x y)
    mul-raise-left-Large-Ring =
      mul-raise-left-Large-Monoid (large-monoid-mul-Large-Ring M)

    mul-raise-raise-Large-Ring :
      {l1 l2 : Level} (l3 l4 : Level) →
      (x : type-Large-Ring M l1) (y : type-Large-Ring M l2) →
      mul-Large-Ring M
        ( raise-Large-Ring M l3 x)
        ( raise-Large-Ring M l4 y) ＝
      raise-Large-Ring M (l3 ⊔ l4) (mul-Large-Ring M x y)
    mul-raise-raise-Large-Ring =
      mul-raise-raise-Large-Monoid (large-monoid-mul-Large-Ring M)
```

### Monoid properties of multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  is-one-prop-Large-Ring : {l : Level} → type-Large-Ring R l → Prop (β l lzero)
  is-one-prop-Large-Ring =
    is-unit-prop-Large-Monoid (large-monoid-mul-Large-Ring R)

  is-one-Large-Ring : {l : Level} → type-Large-Ring R l → UU (β l lzero)
  is-one-Large-Ring x = type-Prop (is-one-prop-Large-Ring x)

  raise-one-Large-Ring : (l : Level) → type-Large-Ring R l
  raise-one-Large-Ring l = raise-Large-Ring R l (one-Large-Ring R)

  is-one-one-Large-Ring : is-one-Large-Ring (one-Large-Ring R)
  is-one-one-Large-Ring =
    is-unit-unit-Large-Monoid (large-monoid-mul-Large-Ring R)

  is-one-raise-one-Large-Ring :
    (l : Level) → is-one-Large-Ring (raise-one-Large-Ring l)
  is-one-raise-one-Large-Ring =
    is-unit-raise-unit-Large-Monoid (large-monoid-mul-Large-Ring R)

  eq-raise-one-is-one-Large-Ring :
    {l : Level} (x : type-Large-Ring R l) →
    is-one-Large-Ring x → x ＝ raise-one-Large-Ring l
  eq-raise-one-is-one-Large-Ring =
    eq-raise-unit-is-unit-Large-Monoid (large-monoid-mul-Large-Ring R)

  left-raise-unit-law-mul-Large-Ring :
    {l1 l2 : Level} (y : type-Large-Ring R l2) →
    mul-Large-Ring R (raise-one-Large-Ring l1) y ＝ raise-Large-Ring R l1 y
  left-raise-unit-law-mul-Large-Ring =
    left-raise-unit-law-mul-Large-Monoid (large-monoid-mul-Large-Ring R)

  right-raise-unit-law-mul-Large-Ring :
    {l1 l2 : Level} (x : type-Large-Ring R l1) →
    mul-Large-Ring R x (raise-one-Large-Ring l2) ＝ raise-Large-Ring R l2 x
  right-raise-unit-law-mul-Large-Ring =
    right-raise-unit-law-mul-Large-Monoid (large-monoid-mul-Large-Ring R)

  eq-left-is-one-law-mul-Large-Ring :
    {l1 l2 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
    is-one-Large-Ring x → mul-Large-Ring R x y ＝ raise-Large-Ring R l1 y
  eq-left-is-one-law-mul-Large-Ring =
    eq-left-is-unit-law-mul-Large-Monoid (large-monoid-mul-Large-Ring R)

  eq-right-is-one-law-mul-Large-Ring :
    {l1 l2 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
    is-one-Large-Ring y → mul-Large-Ring R x y ＝ raise-Large-Ring R l2 x
  eq-right-is-one-law-mul-Large-Ring =
    eq-right-is-unit-law-mul-Large-Monoid (large-monoid-mul-Large-Ring R)

  sim-left-is-one-law-mul-Large-Ring :
    {l1 l2 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
    is-one-Large-Ring x → sim-Large-Ring R (mul-Large-Ring R x y) y
  sim-left-is-one-law-mul-Large-Ring =
    sim-left-is-unit-law-mul-Large-Monoid (large-monoid-mul-Large-Ring R)

  sim-right-is-one-law-mul-Large-Ring :
    {l1 l2 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
    is-one-Large-Ring y → sim-Large-Ring R (mul-Large-Ring R x y) x
  sim-right-is-one-law-mul-Large-Ring =
    sim-right-is-unit-law-mul-Large-Monoid (large-monoid-mul-Large-Ring R)
```

### Zero laws of multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  abstract
    left-is-zero-law-mul-Large-Ring :
      {l1 l2 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
      is-zero-Large-Ring R x → is-zero-Large-Ring R (mul-Large-Ring R x y)
    left-is-zero-law-mul-Large-Ring x y x~0 =
      is-zero-is-idempotent-Large-Ab
        ( large-ab-Large-Ring R)
        ( mul-Large-Ring R x y)
        ( ( inv (right-distributive-mul-add-Large-Ring R x x y)) ∙
          ( ap-mul-Large-Ring R
            ( is-idempotent-is-zero-Large-Ab (large-ab-Large-Ring R) x x~0)
            ( refl)))

    right-is-zero-law-mul-Large-Ring :
      {l1 l2 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
      is-zero-Large-Ring R y → is-zero-Large-Ring R (mul-Large-Ring R x y)
    right-is-zero-law-mul-Large-Ring x y y~0 =
      is-zero-is-idempotent-Large-Ab
        ( large-ab-Large-Ring R)
        ( mul-Large-Ring R x y)
        ( ( inv (left-distributive-mul-add-Large-Ring R x y y)) ∙
          ( ap-mul-Large-Ring R
            ( refl)
            ( is-idempotent-is-zero-Large-Ab
              ( large-ab-Large-Ring R)
              ( y)
              ( y~0))))

    sim-left-zero-law-mul-Large-Ring :
      {l : Level} (x : type-Large-Ring R l) →
      is-zero-Large-Ring R (mul-Large-Ring R (zero-Large-Ring R) x)
    sim-left-zero-law-mul-Large-Ring x =
      left-is-zero-law-mul-Large-Ring _ x (is-zero-zero-Large-Ring R)

    sim-right-zero-law-mul-Large-Ring :
      {l : Level} (x : type-Large-Ring R l) →
      is-zero-Large-Ring R (mul-Large-Ring R x (zero-Large-Ring R))
    sim-right-zero-law-mul-Large-Ring x =
      right-is-zero-law-mul-Large-Ring x _ (is-zero-zero-Large-Ring R)
```

### Negative laws of multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  {l1 l2 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2)
  (let _+R_ = add-Large-Ring R)
  (let _*R_ = mul-Large-Ring R)
  (let neg-R = neg-Large-Ring R)
  where

  open similarity-reasoning-Large-Ring R

  abstract
    left-negative-law-mul-Large-Ring :
      mul-Large-Ring R (neg-Large-Ring R x) y ＝
      neg-Large-Ring R (mul-Large-Ring R x y)
    left-negative-law-mul-Large-Ring =
      eq-sim-Large-Ring R _ _
        ( unique-right-neg-Large-Ring R _ _
          ( similarity-reasoning
            (x *R y) +R (neg-R x *R y)
            ~ (x +R neg-R x) *R y
              by
                sim-eq-Large-Ring R
                  ( inv (right-distributive-mul-add-Large-Ring R x (neg-R x) y))
            ~ zero-Large-Ring R
              by
                left-is-zero-law-mul-Large-Ring R
                  ( x +R neg-R x)
                  ( y)
                  ( sim-right-inverse-law-add-Large-Ring R x)))

    right-negative-law-mul-Large-Ring :
      mul-Large-Ring R x (neg-Large-Ring R y) ＝
      neg-Large-Ring R (mul-Large-Ring R x y)
    right-negative-law-mul-Large-Ring =
      eq-sim-Large-Ring R _ _
        ( unique-right-neg-Large-Ring R _ _
          ( similarity-reasoning
              (x *R y) +R (x *R neg-R y)
              ~ x *R (y +R neg-R y)
                by
                  sim-eq-Large-Ring R
                    ( inv
                      ( left-distributive-mul-add-Large-Ring R x y (neg-R y)))
              ~ zero-Large-Ring R
                by
                  right-is-zero-law-mul-Large-Ring R
                    ( x)
                    ( y +R neg-R y)
                    ( sim-right-inverse-law-add-Large-Ring R y)))
```

### Multiplication by negative one is negation

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  (let _*R_ = mul-Large-Ring R)
  (let neg-R = neg-Large-Ring R)
  where

  neg-one-Large-Ring : type-Large-Ring R lzero
  neg-one-Large-Ring = neg-Large-Ring R (one-Large-Ring R)

  abstract
    left-neg-one-law-mul-Large-Ring :
      {l : Level} (x : type-Large-Ring R l) →
      mul-Large-Ring R neg-one-Large-Ring x ＝ neg-Large-Ring R x
    left-neg-one-law-mul-Large-Ring x =
      equational-reasoning
        neg-one-Large-Ring *R x
        ＝ neg-Large-Ring R (one-Large-Ring R *R x)
          by left-negative-law-mul-Large-Ring R (one-Large-Ring R) x
        ＝ neg-Large-Ring R x
          by ap (neg-Large-Ring R) (sim-left-unit-law-mul-Large-Ring R x)

    right-neg-one-law-mul-Large-Ring :
      {l : Level} (x : type-Large-Ring R l) →
      mul-Large-Ring R x neg-one-Large-Ring ＝ neg-Large-Ring R x
    right-neg-one-law-mul-Large-Ring x =
      equational-reasoning
        x *R neg-one-Large-Ring
        ＝ neg-Large-Ring R (x *R one-Large-Ring R)
          by right-negative-law-mul-Large-Ring R x (one-Large-Ring R)
        ＝ neg-Large-Ring R x
          by ap (neg-Large-Ring R) (sim-right-unit-law-mul-Large-Ring R x)
```

### Distributive laws of multiplication over subtraction

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  {l1 l2 l3 : Level}
  (x : type-Large-Ring R l1)
  (y : type-Large-Ring R l2)
  (z : type-Large-Ring R l3)
  (let _+R_ = add-Large-Ring R)
  (let _*R_ = mul-Large-Ring R)
  (let neg-R = neg-Large-Ring R)
  where

  abstract
    left-distributive-mul-diff-Large-Ring :
      mul-Large-Ring R x (diff-Large-Ring R y z) ＝
      diff-Large-Ring R (mul-Large-Ring R x y) (mul-Large-Ring R x z)
    left-distributive-mul-diff-Large-Ring =
      ( left-distributive-mul-add-Large-Ring R x y (neg-R z)) ∙
      ( ap-add-Large-Ring R refl (right-negative-law-mul-Large-Ring R x z))

    right-distributive-mul-diff-Large-Ring :
      mul-Large-Ring R (diff-Large-Ring R x y) z ＝
      diff-Large-Ring R (mul-Large-Ring R x z) (mul-Large-Ring R y z)
    right-distributive-mul-diff-Large-Ring =
      ( right-distributive-mul-add-Large-Ring R x (neg-R y) z) ∙
      ( ap-add-Large-Ring R refl (left-negative-law-mul-Large-Ring R y z))
```

### Small rings from large rings

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  ring-Large-Ring : (l : Level) → Ring (α l)
  ring-Large-Ring l =
    ( ab-Large-Ab (large-ab-Large-Ring R) l ,
      ( mul-Large-Ring R , associative-mul-Large-Ring R) ,
      is-unital-Monoid
        ( monoid-Large-Monoid (large-monoid-mul-Large-Ring R) l) ,
      left-distributive-mul-add-Large-Ring R ,
      right-distributive-mul-add-Large-Ring R)
```

### The raise operation is a ring homomorphism

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  (l1 l2 : Level)
  where

  hom-raise-Large-Ring :
    hom-Ring
      ( ring-Large-Ring R l1)
      ( ring-Large-Ring R (l1 ⊔ l2))
  hom-raise-Large-Ring =
    ( hom-raise-Large-Ab (large-ab-Large-Ring R) l1 l2 ,
      inv
        ( mul-raise-raise-Large-Monoid
          ( large-monoid-mul-Large-Ring R)
          ( l2)
          ( l2)
          ( _)
          ( _)) ,
      raise-raise-Large-Ring R (one-Large-Ring R))
```
