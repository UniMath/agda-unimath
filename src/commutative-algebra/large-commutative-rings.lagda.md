# Large commutative rings

```agda
module commutative-algebra.large-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.homomorphisms-commutative-rings

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositions
open import foundation.embeddings
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.cumulative-large-sets
open import foundation.similarity-preserving-binary-maps-cumulative-large-sets
open import foundation.similarity-preserving-maps-cumulative-large-sets
open import foundation.large-binary-relations
open import foundation.large-similarity-relations
open import foundation.sets
open import foundation.universe-levels
open import group-theory.large-monoids
open import group-theory.large-commutative-monoids

open import ring-theory.large-rings
```

</details>

## Idea

A {{#concept "large commutative ring" Agda=Large-Commutative-Ring}} is a
[large ring](ring-theory.large-rings.md) with a commutative multiplicative
operation.

## Definition

```agda
record Large-Commutative-Ring
  (α : Level → Level) (β : Level → Level → Level) : UUω where

  constructor
    make-Large-Commutative-Ring

  field
    large-ring-Large-Commutative-Ring : Large-Ring α β

  cumulative-large-set-Large-Commutative-Ring : Cumulative-Large-Set α β
  cumulative-large-set-Large-Commutative-Ring =
    cumulative-large-set-Large-Ring large-ring-Large-Commutative-Ring

  type-Large-Commutative-Ring : (l : Level) → UU (α l)
  type-Large-Commutative-Ring =
    type-Large-Ring large-ring-Large-Commutative-Ring

  set-Large-Commutative-Ring : (l : Level) → Set (α l)
  set-Large-Commutative-Ring = set-Large-Ring large-ring-Large-Commutative-Ring

  add-Large-Commutative-Ring :
    {l1 l2 : Level} →
    type-Large-Commutative-Ring l1 →
    type-Large-Commutative-Ring l2 →
    type-Large-Commutative-Ring (l1 ⊔ l2)
  add-Large-Commutative-Ring = add-Large-Ring large-ring-Large-Commutative-Ring

  add-Large-Commutative-Ring' :
    {l1 l2 : Level} →
    type-Large-Commutative-Ring l1 →
    type-Large-Commutative-Ring l2 →
    type-Large-Commutative-Ring (l1 ⊔ l2)
  add-Large-Commutative-Ring' x y = add-Large-Commutative-Ring y x

  mul-Large-Commutative-Ring :
    {l1 l2 : Level} →
    type-Large-Commutative-Ring l1 →
    type-Large-Commutative-Ring l2 →
    type-Large-Commutative-Ring (l1 ⊔ l2)
  mul-Large-Commutative-Ring = mul-Large-Ring large-ring-Large-Commutative-Ring

  neg-Large-Commutative-Ring :
    {l : Level} →
    type-Large-Commutative-Ring l → type-Large-Commutative-Ring l
  neg-Large-Commutative-Ring = neg-Large-Ring large-ring-Large-Commutative-Ring

  diff-Large-Commutative-Ring :
    {l1 l2 : Level} →
    type-Large-Commutative-Ring l1 →
    type-Large-Commutative-Ring l2 →
    type-Large-Commutative-Ring (l1 ⊔ l2)
  diff-Large-Commutative-Ring =
    diff-Large-Ring large-ring-Large-Commutative-Ring

  field
    commutative-mul-Large-Commutative-Ring :
      {l1 l2 : Level} →
      (a : type-Large-Commutative-Ring l1) →
      (b : type-Large-Commutative-Ring l2) →
      mul-Large-Commutative-Ring a b ＝ mul-Large-Commutative-Ring b a

open Large-Commutative-Ring public
```

## Properties

### Similarity

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  where

  large-similarity-relation-Large-Commutative-Ring :
    Large-Similarity-Relation β (type-Large-Commutative-Ring R)
  large-similarity-relation-Large-Commutative-Ring =
    large-similarity-relation-Large-Ring (large-ring-Large-Commutative-Ring R)

  sim-prop-Large-Commutative-Ring :
    Large-Relation-Prop β (type-Large-Commutative-Ring R)
  sim-prop-Large-Commutative-Ring =
    sim-prop-Large-Ring (large-ring-Large-Commutative-Ring R)

  sim-Large-Commutative-Ring : Large-Relation β (type-Large-Commutative-Ring R)
  sim-Large-Commutative-Ring = sim-Large-Ring (large-ring-Large-Commutative-Ring R)

  refl-sim-Large-Commutative-Ring :
    is-reflexive-Large-Relation (type-Large-Commutative-Ring R) sim-Large-Commutative-Ring
  refl-sim-Large-Commutative-Ring =
    refl-sim-Large-Ring (large-ring-Large-Commutative-Ring R)

  symmetric-sim-Large-Commutative-Ring :
    is-symmetric-Large-Relation (type-Large-Commutative-Ring R) sim-Large-Commutative-Ring
  symmetric-sim-Large-Commutative-Ring =
    symmetric-sim-Large-Ring (large-ring-Large-Commutative-Ring R)

  transitive-sim-Large-Commutative-Ring :
    is-transitive-Large-Relation (type-Large-Commutative-Ring R) sim-Large-Commutative-Ring
  transitive-sim-Large-Commutative-Ring =
    transitive-sim-Large-Ring (large-ring-Large-Commutative-Ring R)

  sim-eq-Large-Commutative-Ring :
    {l : Level} {x y : type-Large-Commutative-Ring R l} → x ＝ y → sim-Large-Commutative-Ring x y
  sim-eq-Large-Commutative-Ring = sim-eq-Large-Ring (large-ring-Large-Commutative-Ring R)

  eq-sim-Large-Commutative-Ring :
    {l : Level} (x y : type-Large-Commutative-Ring R l) → sim-Large-Commutative-Ring x y → x ＝ y
  eq-sim-Large-Commutative-Ring = eq-sim-Large-Ring (large-ring-Large-Commutative-Ring R)
```

### Similarity reasoning on large rings

```agda
module
  similarity-reasoning-Large-Commutative-Ring
    {α : Level → Level} {β : Level → Level → Level} (R : Large-Commutative-Ring α β)
  where

  open similarity-reasoning-Large-Ring (large-ring-Large-Commutative-Ring R) public
```

### Raising universe levels

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  where

  raise-Large-Commutative-Ring :
    {l0 : Level} (l : Level) →
    type-Large-Commutative-Ring R l0 → type-Large-Commutative-Ring R (l0 ⊔ l)
  raise-Large-Commutative-Ring = raise-Large-Ring (large-ring-Large-Commutative-Ring R)

  sim-raise-Large-Commutative-Ring :
    {l0 : Level} (l : Level) (x : type-Large-Commutative-Ring R l0) →
    sim-Large-Commutative-Ring R x (raise-Large-Commutative-Ring l x)
  sim-raise-Large-Commutative-Ring =
    sim-raise-Large-Ring (large-ring-Large-Commutative-Ring R)

  sim-raise-Large-Commutative-Ring' :
    {l0 : Level} (l : Level) (x : type-Large-Commutative-Ring R l0) →
    sim-Large-Commutative-Ring R (raise-Large-Commutative-Ring l x) x
  sim-raise-Large-Commutative-Ring' =
    sim-raise-Large-Ring' (large-ring-Large-Commutative-Ring R)

  eq-raise-Large-Commutative-Ring :
    {l : Level} (x : type-Large-Commutative-Ring R l) → raise-Large-Commutative-Ring l x ＝ x
  eq-raise-Large-Commutative-Ring =
    eq-raise-Large-Ring (large-ring-Large-Commutative-Ring R)

  is-emb-raise-Large-Commutative-Ring :
    (l1 l2 : Level) → is-emb (raise-Large-Commutative-Ring {l1} l2)
  is-emb-raise-Large-Commutative-Ring =
    is-emb-raise-Large-Ring (large-ring-Large-Commutative-Ring R)

  emb-raise-Large-Commutative-Ring :
    (l1 l2 : Level) → type-Large-Commutative-Ring R l1 ↪ type-Large-Commutative-Ring R (l1 ⊔ l2)
  emb-raise-Large-Commutative-Ring =
    emb-raise-Large-Ring (large-ring-Large-Commutative-Ring R)

  raise-raise-Large-Commutative-Ring :
    {l0 l1 l2 : Level} (x : type-Large-Commutative-Ring R l0) →
    raise-Large-Commutative-Ring l1 (raise-Large-Commutative-Ring l2 x) ＝
    raise-Large-Commutative-Ring (l1 ⊔ l2) x
  raise-raise-Large-Commutative-Ring =
    raise-raise-Large-Ring (large-ring-Large-Commutative-Ring R)

  eq-raise-sim-Large-Commutative-Ring :
    {l1 l2 : Level} (x : type-Large-Commutative-Ring R l1) (y : type-Large-Commutative-Ring R l2) →
    sim-Large-Commutative-Ring R x y → raise-Large-Commutative-Ring l2 x ＝ raise-Large-Commutative-Ring l1 y
  eq-raise-sim-Large-Commutative-Ring =
    eq-raise-sim-Large-Ring (large-ring-Large-Commutative-Ring R)

  sim-eq-raise-Large-Commutative-Ring :
    {l1 l2 : Level} (x : type-Large-Commutative-Ring R l1) (y : type-Large-Commutative-Ring R l2) →
    raise-Large-Commutative-Ring l2 x ＝ raise-Large-Commutative-Ring l1 y → sim-Large-Commutative-Ring R x y
  sim-eq-raise-Large-Commutative-Ring =
    sim-eq-raise-Large-Ring (large-ring-Large-Commutative-Ring R)

  eq-raise-iff-sim-Large-Commutative-Ring :
    {l1 l2 : Level} →
    (x : type-Large-Commutative-Ring R l1) (y : type-Large-Commutative-Ring R l2) →
    ( sim-Large-Commutative-Ring R x y ↔
      ( raise-Large-Commutative-Ring l2 x ＝ raise-Large-Commutative-Ring l1 y))
  eq-raise-iff-sim-Large-Commutative-Ring =
    eq-raise-iff-sim-Large-Ring (large-ring-Large-Commutative-Ring R)

  eq-raise-sim-Large-Commutative-Ring' :
    {l1 l2 : Level}
    (x : type-Large-Commutative-Ring R (l1 ⊔ l2)) (y : type-Large-Commutative-Ring R l2) →
    sim-Large-Commutative-Ring R x y → x ＝ raise-Large-Commutative-Ring l1 y
  eq-raise-sim-Large-Commutative-Ring' =
    eq-raise-sim-Large-Ring' (large-ring-Large-Commutative-Ring R)
```

### Similarity preservation of addition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Commutative-Ring α β)
  where

  sim-preserving-binary-operator-add-Large-Commutative-Ring :
    sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Commutative-Ring R)
  sim-preserving-binary-operator-add-Large-Commutative-Ring =
    sim-preserving-binary-operator-add-Large-Ring (large-ring-Large-Commutative-Ring R)

  preserves-sim-add-Large-Commutative-Ring :
    preserves-sim-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Commutative-Ring R)
      ( add-Large-Commutative-Ring R)
  preserves-sim-add-Large-Commutative-Ring =
    preserves-sim-add-Large-Ring (large-ring-Large-Commutative-Ring R)

  sim-preserving-map-left-add-Large-Commutative-Ring :
    {l : Level} (x : type-Large-Commutative-Ring R l) →
    sim-preserving-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Commutative-Ring R)
  sim-preserving-map-left-add-Large-Commutative-Ring =
    sim-preserving-map-left-add-Large-Ring (large-ring-Large-Commutative-Ring R)

  preserves-sim-left-add-Large-Commutative-Ring :
    {l : Level} (x : type-Large-Commutative-Ring R l) →
    preserves-sim-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Commutative-Ring R)
      ( add-Large-Commutative-Ring R x)
  preserves-sim-left-add-Large-Commutative-Ring =
    preserves-sim-left-add-Large-Ring (large-ring-Large-Commutative-Ring R)

  sim-preserving-map-right-add-Large-Commutative-Ring :
    {l : Level} (y : type-Large-Commutative-Ring R l) →
    sim-preserving-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Commutative-Ring R)
  sim-preserving-map-right-add-Large-Commutative-Ring =
    sim-preserving-map-right-add-Large-Ring
      ( large-ring-Large-Commutative-Ring R)

  preserves-sim-right-add-Large-Commutative-Ring :
    {l : Level} (y : type-Large-Commutative-Ring R l) →
    preserves-sim-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Commutative-Ring R)
      ( add-Large-Commutative-Ring' R y)
  preserves-sim-right-add-Large-Commutative-Ring =
    preserves-sim-right-add-Large-Ring (large-ring-Large-Commutative-Ring R)
```

### Raising universe levels in addition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Commutative-Ring α β)
  where

  abstract
    add-raise-right-Large-Commutative-Ring :
      {l1 l2 : Level} (l3 : Level) →
      (x : type-Large-Commutative-Ring R l1) (y : type-Large-Commutative-Ring R l2) →
      add-Large-Commutative-Ring R x (raise-Large-Commutative-Ring R l3 y) ＝
      raise-Large-Commutative-Ring R l3 (add-Large-Commutative-Ring R x y)
    add-raise-right-Large-Commutative-Ring =
      add-raise-right-Large-Ring (large-ring-Large-Commutative-Ring R)

    add-raise-left-Large-Commutative-Ring :
      {l1 l2 : Level} (l3 : Level) →
      (x : type-Large-Commutative-Ring R l1) (y : type-Large-Commutative-Ring R l2) →
      add-Large-Commutative-Ring R (raise-Large-Commutative-Ring R l3 x) y ＝
      raise-Large-Commutative-Ring R l3 (add-Large-Commutative-Ring R x y)
    add-raise-left-Large-Commutative-Ring =
      add-raise-left-Large-Ring (large-ring-Large-Commutative-Ring R)

    add-raise-raise-Large-Commutative-Ring :
      {l1 l2 : Level} (l3 l4 : Level) →
      (x : type-Large-Commutative-Ring R l1) (y : type-Large-Commutative-Ring R l2) →
      add-Large-Commutative-Ring R
        ( raise-Large-Commutative-Ring R l3 x)
        ( raise-Large-Commutative-Ring R l4 y) ＝
      raise-Large-Commutative-Ring R (l3 ⊔ l4) (add-Large-Commutative-Ring R x y)
    add-raise-raise-Large-Commutative-Ring =
      add-raise-raise-Large-Ring (large-ring-Large-Commutative-Ring R)
```

### The negation operation preserves similarity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Commutative-Ring α β)
  where

  sim-preserving-endomap-neg-Large-Commutative-Ring :
    sim-preserving-endomap-Cumulative-Large-Set
      ( id)
      ( cumulative-large-set-Large-Commutative-Ring R)
  sim-preserving-endomap-neg-Large-Commutative-Ring =
    sim-preserving-endomap-neg-Large-Ring (large-ring-Large-Commutative-Ring R)

  preserves-sim-neg-Large-Commutative-Ring :
    preserves-sim-endomap-Cumulative-Large-Set
      ( id)
      ( cumulative-large-set-Large-Commutative-Ring R)
      ( neg-Large-Commutative-Ring R)
  preserves-sim-neg-Large-Commutative-Ring =
    preserves-sim-neg-Large-Ring (large-ring-Large-Commutative-Ring R)
```

### Semigroup laws of addition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Commutative-Ring α β)
  where

  associative-add-Large-Commutative-Ring :
    {l1 l2 l3 : Level}
    (x : type-Large-Commutative-Ring R l1)
    (y : type-Large-Commutative-Ring R l2)
    (z : type-Large-Commutative-Ring R l3) →
    add-Large-Commutative-Ring R (add-Large-Commutative-Ring R x y) z ＝
    add-Large-Commutative-Ring R x (add-Large-Commutative-Ring R y z)
  associative-add-Large-Commutative-Ring =
    associative-add-Large-Ring (large-ring-Large-Commutative-Ring R)
```

### Monoid laws of addition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Commutative-Ring α β)
  where

  zero-Large-Commutative-Ring : type-Large-Commutative-Ring R lzero
  zero-Large-Commutative-Ring = zero-Large-Ring (large-ring-Large-Commutative-Ring R)

  raise-zero-Large-Commutative-Ring : (l : Level) → type-Large-Commutative-Ring R l
  raise-zero-Large-Commutative-Ring = raise-zero-Large-Ring (large-ring-Large-Commutative-Ring R)

  is-zero-prop-Large-Commutative-Ring : {l : Level} → type-Large-Commutative-Ring R l → Prop (β l lzero)
  is-zero-prop-Large-Commutative-Ring = is-zero-prop-Large-Ring (large-ring-Large-Commutative-Ring R)

  is-zero-Large-Commutative-Ring : {l : Level} → type-Large-Commutative-Ring R l → UU (β l lzero)
  is-zero-Large-Commutative-Ring x = type-Prop (is-zero-prop-Large-Commutative-Ring x)

  is-zero-zero-Large-Commutative-Ring : is-zero-Large-Commutative-Ring zero-Large-Commutative-Ring
  is-zero-zero-Large-Commutative-Ring =
    is-zero-zero-Large-Ring (large-ring-Large-Commutative-Ring R)

  is-zero-raise-zero-Large-Commutative-Ring :
    (l : Level) → is-zero-Large-Commutative-Ring (raise-zero-Large-Commutative-Ring l)
  is-zero-raise-zero-Large-Commutative-Ring =
    is-zero-raise-zero-Large-Ring (large-ring-Large-Commutative-Ring R)

  eq-raise-zero-is-zero-Large-Commutative-Ring :
    {l : Level} (x : type-Large-Commutative-Ring R l) →
    is-zero-Large-Commutative-Ring x → x ＝ raise-zero-Large-Commutative-Ring l
  eq-raise-zero-is-zero-Large-Commutative-Ring =
    eq-raise-zero-is-zero-Large-Ring (large-ring-Large-Commutative-Ring R)

  left-unit-law-add-Large-Commutative-Ring :
    {l : Level} (x : type-Large-Commutative-Ring R l) →
    add-Large-Commutative-Ring R zero-Large-Commutative-Ring x ＝ x
  left-unit-law-add-Large-Commutative-Ring =
    left-unit-law-add-Large-Ring (large-ring-Large-Commutative-Ring R)

  right-unit-law-add-Large-Commutative-Ring :
    {l : Level} (x : type-Large-Commutative-Ring R l) →
    add-Large-Commutative-Ring R x zero-Large-Commutative-Ring ＝ x
  right-unit-law-add-Large-Commutative-Ring =
    right-unit-law-add-Large-Ring (large-ring-Large-Commutative-Ring R)

  left-raise-unit-law-add-Large-Commutative-Ring :
    {l1 l2 : Level} (y : type-Large-Commutative-Ring R l2) →
    add-Large-Commutative-Ring R (raise-zero-Large-Commutative-Ring l1) y ＝ raise-Large-Commutative-Ring R l1 y
  left-raise-unit-law-add-Large-Commutative-Ring =
    left-raise-unit-law-add-Large-Ring (large-ring-Large-Commutative-Ring R)

  right-raise-unit-law-add-Large-Commutative-Ring :
    {l1 l2 : Level} (x : type-Large-Commutative-Ring R l1) →
    add-Large-Commutative-Ring R x (raise-zero-Large-Commutative-Ring l2) ＝ raise-Large-Commutative-Ring R l2 x
  right-raise-unit-law-add-Large-Commutative-Ring =
    right-raise-unit-law-add-Large-Ring (large-ring-Large-Commutative-Ring R)

  eq-left-is-zero-law-add-Large-Commutative-Ring :
    {l1 l2 : Level} (x : type-Large-Commutative-Ring R l1) (y : type-Large-Commutative-Ring R l2) →
    is-zero-Large-Commutative-Ring x → add-Large-Commutative-Ring R x y ＝ raise-Large-Commutative-Ring R l1 y
  eq-left-is-zero-law-add-Large-Commutative-Ring =
    eq-left-is-zero-law-add-Large-Ring (large-ring-Large-Commutative-Ring R)

  eq-right-is-zero-law-add-Large-Commutative-Ring :
    {l1 l2 : Level} (x : type-Large-Commutative-Ring R l1) (y : type-Large-Commutative-Ring R l2) →
    is-zero-Large-Commutative-Ring y → add-Large-Commutative-Ring R x y ＝ raise-Large-Commutative-Ring R l2 x
  eq-right-is-zero-law-add-Large-Commutative-Ring =
    eq-right-is-zero-law-add-Large-Ring (large-ring-Large-Commutative-Ring R)

  sim-left-is-zero-law-add-Large-Commutative-Ring :
    {l1 l2 : Level} (x : type-Large-Commutative-Ring R l1) (y : type-Large-Commutative-Ring R l2) →
    is-zero-Large-Commutative-Ring x → sim-Large-Commutative-Ring R (add-Large-Commutative-Ring R x y) y
  sim-left-is-zero-law-add-Large-Commutative-Ring =
    sim-left-is-zero-law-add-Large-Ring (large-ring-Large-Commutative-Ring R)

  sim-right-is-zero-law-add-Large-Commutative-Ring :
    {l1 l2 : Level} (x : type-Large-Commutative-Ring R l1) (y : type-Large-Commutative-Ring R l2) →
    is-zero-Large-Commutative-Ring y → sim-Large-Commutative-Ring R (add-Large-Commutative-Ring R x y) x
  sim-right-is-zero-law-add-Large-Commutative-Ring =
    sim-right-is-zero-law-add-Large-Ring (large-ring-Large-Commutative-Ring R)
```

### Group laws of addition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Commutative-Ring α β)
  where

  abstract
    sim-left-inverse-law-add-Large-Commutative-Ring :
      {l : Level} (x : type-Large-Commutative-Ring R l) →
      is-zero-Large-Commutative-Ring R (add-Large-Commutative-Ring R (neg-Large-Commutative-Ring R x) x)
    sim-left-inverse-law-add-Large-Commutative-Ring =
      sim-left-inverse-law-add-Large-Ring (large-ring-Large-Commutative-Ring R)

    sim-right-inverse-law-add-Large-Commutative-Ring :
      {l : Level} (x : type-Large-Commutative-Ring R l) →
      is-zero-Large-Commutative-Ring R (add-Large-Commutative-Ring R x (neg-Large-Commutative-Ring R x))
    sim-right-inverse-law-add-Large-Commutative-Ring =
      sim-right-inverse-law-add-Large-Ring (large-ring-Large-Commutative-Ring R)

    eq-left-inverse-law-add-Large-Commutative-Ring :
      {l : Level} (x : type-Large-Commutative-Ring R l) →
      add-Large-Commutative-Ring R (neg-Large-Commutative-Ring R x) x ＝ raise-zero-Large-Commutative-Ring R l
    eq-left-inverse-law-add-Large-Commutative-Ring =
      eq-left-inverse-law-add-Large-Ring (large-ring-Large-Commutative-Ring R)

    eq-right-inverse-law-add-Large-Commutative-Ring :
      {l : Level} (x : type-Large-Commutative-Ring R l) →
      add-Large-Commutative-Ring R x (neg-Large-Commutative-Ring R x) ＝ raise-zero-Large-Commutative-Ring R l
    eq-right-inverse-law-add-Large-Commutative-Ring =
      eq-right-inverse-law-add-Large-Ring (large-ring-Large-Commutative-Ring R)

    unique-left-neg-Large-Commutative-Ring :
      {l1 l2 : Level} (x : type-Large-Commutative-Ring R l1) (y : type-Large-Commutative-Ring R l2) →
      is-zero-Large-Commutative-Ring R (add-Large-Commutative-Ring R x y) →
      sim-Large-Commutative-Ring R x (neg-Large-Commutative-Ring R y)
    unique-left-neg-Large-Commutative-Ring =
      unique-left-neg-Large-Ring (large-ring-Large-Commutative-Ring R)

    unique-right-neg-Large-Commutative-Ring :
      {l1 l2 : Level} (x : type-Large-Commutative-Ring R l1) (y : type-Large-Commutative-Ring R l2) →
      is-zero-Large-Commutative-Ring R (add-Large-Commutative-Ring R x y) →
      sim-Large-Commutative-Ring R y (neg-Large-Commutative-Ring R x)
    unique-right-neg-Large-Commutative-Ring =
      unique-right-neg-Large-Ring (large-ring-Large-Commutative-Ring R)

    distributive-neg-add-Large-Commutative-Ring :
      {l1 l2 : Level} (x : type-Large-Commutative-Ring R l1) (y : type-Large-Commutative-Ring R l2) →
      neg-Large-Commutative-Ring R (add-Large-Commutative-Ring R x y) ＝
      add-Large-Commutative-Ring R (neg-Large-Commutative-Ring R x) (neg-Large-Commutative-Ring R y)
    distributive-neg-add-Large-Commutative-Ring x y =
      distributive-neg-add-Large-Ring (large-ring-Large-Commutative-Ring R) x y

    neg-is-zero-Large-Commutative-Ring :
      {l : Level} (x : type-Large-Commutative-Ring R l) →
      is-zero-Large-Commutative-Ring R x → is-zero-Large-Commutative-Ring R (neg-Large-Commutative-Ring R x)
    neg-is-zero-Large-Commutative-Ring = neg-is-zero-Large-Ring (large-ring-Large-Commutative-Ring R)

    neg-zero-Large-Commutative-Ring :
      neg-Large-Commutative-Ring R (zero-Large-Commutative-Ring R) ＝ zero-Large-Commutative-Ring R
    neg-zero-Large-Commutative-Ring = neg-zero-Large-Ring (large-ring-Large-Commutative-Ring R)

    neg-raise-zero-Large-Commutative-Ring :
      (l : Level) →
      neg-Large-Commutative-Ring R (raise-zero-Large-Commutative-Ring R l) ＝ raise-zero-Large-Commutative-Ring R l
    neg-raise-zero-Large-Commutative-Ring =
      neg-raise-zero-Large-Ring (large-ring-Large-Commutative-Ring R)

    neg-neg-Large-Commutative-Ring :
      {l : Level} (x : type-Large-Commutative-Ring R l) →
      neg-Large-Commutative-Ring R (neg-Large-Commutative-Ring R x) ＝ x
    neg-neg-Large-Commutative-Ring = neg-neg-Large-Ring (large-ring-Large-Commutative-Ring R)
```

### Cancellation laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Commutative-Ring α β)
  {l1 l2 : Level} (x : type-Large-Commutative-Ring R l1) (y : type-Large-Commutative-Ring R l2)
  where

  abstract
    sim-cancel-left-diff-add-Large-Commutative-Ring :
      sim-Large-Commutative-Ring R
        ( add-Large-Commutative-Ring R (neg-Large-Commutative-Ring R x) (add-Large-Commutative-Ring R x y))
        ( y)
    sim-cancel-left-diff-add-Large-Commutative-Ring =
      sim-cancel-left-diff-add-Large-Ring (large-ring-Large-Commutative-Ring R) x y

    sim-cancel-left-add-diff-Large-Commutative-Ring :
      sim-Large-Commutative-Ring R
        ( add-Large-Commutative-Ring R x (add-Large-Commutative-Ring R (neg-Large-Commutative-Ring R x) y))
        ( y)
    sim-cancel-left-add-diff-Large-Commutative-Ring =
      sim-cancel-left-add-diff-Large-Ring (large-ring-Large-Commutative-Ring R) x y

    sim-cancel-right-diff-add-Large-Commutative-Ring :
      sim-Large-Commutative-Ring R
        ( add-Large-Commutative-Ring R (add-Large-Commutative-Ring R y (neg-Large-Commutative-Ring R x)) x)
        ( y)
    sim-cancel-right-diff-add-Large-Commutative-Ring =
      sim-cancel-right-diff-add-Large-Ring (large-ring-Large-Commutative-Ring R) x y

    sim-cancel-right-add-diff-Large-Commutative-Ring :
      sim-Large-Commutative-Ring R
        ( add-Large-Commutative-Ring R (add-Large-Commutative-Ring R y x) (neg-Large-Commutative-Ring R x))
        ( y)
    sim-cancel-right-add-diff-Large-Commutative-Ring =
      sim-cancel-right-add-diff-Large-Ring (large-ring-Large-Commutative-Ring R) x y

    eq-cancel-left-diff-add-Large-Commutative-Ring :
      add-Large-Commutative-Ring R (neg-Large-Commutative-Ring R x) (add-Large-Commutative-Ring R x y) ＝
      raise-Large-Commutative-Ring R l1 y
    eq-cancel-left-diff-add-Large-Commutative-Ring =
      eq-cancel-left-diff-add-Large-Ring (large-ring-Large-Commutative-Ring R) x y

    eq-cancel-left-add-diff-Large-Commutative-Ring :
      add-Large-Commutative-Ring R x (add-Large-Commutative-Ring R (neg-Large-Commutative-Ring R x) y) ＝
      raise-Large-Commutative-Ring R l1 y
    eq-cancel-left-add-diff-Large-Commutative-Ring =
      eq-cancel-left-add-diff-Large-Ring (large-ring-Large-Commutative-Ring R) x y

    eq-cancel-right-diff-add-Large-Commutative-Ring :
      add-Large-Commutative-Ring R (add-Large-Commutative-Ring R y (neg-Large-Commutative-Ring R x)) x ＝
      raise-Large-Commutative-Ring R l1 y
    eq-cancel-right-diff-add-Large-Commutative-Ring =
      eq-cancel-right-diff-add-Large-Ring (large-ring-Large-Commutative-Ring R) x y

    eq-cancel-right-add-diff-Large-Commutative-Ring :
      add-Large-Commutative-Ring R (add-Large-Commutative-Ring R y x) (neg-Large-Commutative-Ring R x) ＝
      raise-Large-Commutative-Ring R l1 y
    eq-cancel-right-add-diff-Large-Commutative-Ring =
      eq-cancel-right-add-diff-Large-Ring (large-ring-Large-Commutative-Ring R) x y
```

### Addition reflects similarity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Commutative-Ring α β)
  {l1 l2 l3 : Level}
  (z : type-Large-Commutative-Ring R l3)
  (x : type-Large-Commutative-Ring R l1)
  (y : type-Large-Commutative-Ring R l2)
  where

  abstract
    reflects-sim-right-add-Large-Commutative-Ring :
      sim-Large-Commutative-Ring R (add-Large-Commutative-Ring R x z) (add-Large-Commutative-Ring R y z) →
      sim-Large-Commutative-Ring R x y
    reflects-sim-right-add-Large-Commutative-Ring =
      reflects-sim-right-add-Large-Ring (large-ring-Large-Commutative-Ring R) z x y

    reflects-sim-left-add-Large-Commutative-Ring :
      sim-Large-Commutative-Ring R (add-Large-Commutative-Ring R z x) (add-Large-Commutative-Ring R z y) →
      sim-Large-Commutative-Ring R x y
    reflects-sim-left-add-Large-Commutative-Ring =
      reflects-sim-left-add-Large-Ring (large-ring-Large-Commutative-Ring R) z x y
```

### Addition on the left or right in a large ring is an embedding

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Commutative-Ring α β)
  {l1 : Level} (l2 : Level) (x : type-Large-Commutative-Ring R l1)
  where

  abstract
    is-emb-left-add-Large-Commutative-Ring :
      is-emb (add-Large-Commutative-Ring R {l2 = l2} x)
    is-emb-left-add-Large-Commutative-Ring =
      is-emb-left-add-Large-Ring (large-ring-Large-Commutative-Ring R) l2 x

    is-emb-right-add-Large-Commutative-Ring :
      is-emb (add-Large-Commutative-Ring' R {l2 = l2} x)
    is-emb-right-add-Large-Commutative-Ring =
      is-emb-right-add-Large-Ring (large-ring-Large-Commutative-Ring R) l2 x
```

### Small commutative rings from large commutative rings

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  where

  commutative-ring-Large-Commutative-Ring : (l : Level) → Commutative-Ring (α l)
  commutative-ring-Large-Commutative-Ring l =
    ( ring-Large-Ring (large-ring-Large-Commutative-Ring R) l ,
      commutative-mul-Large-Commutative-Ring R)
```

### The multiplicative large commutative monoid of a large commutative ring

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  where

  large-monoid-mul-Large-Commutative-Ring : Large-Monoid α β
  large-monoid-mul-Large-Commutative-Ring =
    large-monoid-mul-Large-Ring
      ( large-ring-Large-Commutative-Ring R)

  large-commutative-monoid-mul-Large-Commutative-Ring :
    Large-Commutative-Monoid α β
  large-commutative-monoid-mul-Large-Commutative-Ring =
    make-Large-Commutative-Monoid
      ( large-monoid-mul-Large-Commutative-Ring)
      ( commutative-mul-Large-Commutative-Ring R)
```

### Floating raised universe levels out of multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Commutative-Ring α β)
  where

  abstract
    mul-raise-right-Large-Commutative-Ring :
      {l1 l2 : Level} (l3 : Level) →
      (x : type-Large-Commutative-Ring M l1) (y : type-Large-Commutative-Ring M l2) →
      mul-Large-Commutative-Ring M x (raise-Large-Commutative-Ring M l3 y) ＝
      raise-Large-Commutative-Ring M l3 (mul-Large-Commutative-Ring M x y)
    mul-raise-right-Large-Commutative-Ring =
      mul-raise-right-Large-Monoid (large-monoid-mul-Large-Commutative-Ring M)

    mul-raise-left-Large-Commutative-Ring :
      {l1 l2 : Level} (l3 : Level) →
      (x : type-Large-Commutative-Ring M l1) (y : type-Large-Commutative-Ring M l2) →
      mul-Large-Commutative-Ring M (raise-Large-Commutative-Ring M l3 x) y ＝
      raise-Large-Commutative-Ring M l3 (mul-Large-Commutative-Ring M x y)
    mul-raise-left-Large-Commutative-Ring =
      mul-raise-left-Large-Monoid (large-monoid-mul-Large-Commutative-Ring M)

    mul-raise-raise-Large-Commutative-Ring :
      {l1 l2 : Level} (l3 l4 : Level) →
      (x : type-Large-Commutative-Ring M l1) (y : type-Large-Commutative-Ring M l2) →
      mul-Large-Commutative-Ring M
        ( raise-Large-Commutative-Ring M l3 x)
        ( raise-Large-Commutative-Ring M l4 y) ＝
      raise-Large-Commutative-Ring M (l3 ⊔ l4) (mul-Large-Commutative-Ring M x y)
    mul-raise-raise-Large-Commutative-Ring =
      mul-raise-raise-Large-Monoid (large-monoid-mul-Large-Commutative-Ring M)
```

### Monoid properties of multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Commutative-Ring α β)
  where

  is-one-prop-Large-Commutative-Ring :
    {l : Level} → type-Large-Commutative-Ring R l → Prop (β l lzero)
  is-one-prop-Large-Commutative-Ring =
    is-one-prop-Large-Ring (large-ring-Large-Commutative-Ring R)

  is-one-Large-Commutative-Ring :
    {l : Level} → type-Large-Commutative-Ring R l → UU (β l lzero)
  is-one-Large-Commutative-Ring =
    is-one-Large-Ring (large-ring-Large-Commutative-Ring R)

  one-Large-Commutative-Ring : type-Large-Commutative-Ring R lzero
  one-Large-Commutative-Ring =
    one-Large-Ring (large-ring-Large-Commutative-Ring R)

  raise-one-Large-Commutative-Ring :
    (l : Level) → type-Large-Commutative-Ring R l
  raise-one-Large-Commutative-Ring =
    raise-one-Large-Ring (large-ring-Large-Commutative-Ring R)

  is-one-one-Large-Commutative-Ring :
    is-one-Large-Commutative-Ring one-Large-Commutative-Ring
  is-one-one-Large-Commutative-Ring =
    is-one-one-Large-Ring (large-ring-Large-Commutative-Ring R)

  is-one-raise-one-Large-Commutative-Ring :
    (l : Level) →
    is-one-Large-Commutative-Ring (raise-one-Large-Commutative-Ring l)
  is-one-raise-one-Large-Commutative-Ring =
    is-one-raise-one-Large-Ring (large-ring-Large-Commutative-Ring R)

  eq-raise-one-is-one-Large-Commutative-Ring :
    {l : Level} (x : type-Large-Commutative-Ring R l) →
    is-one-Large-Commutative-Ring x → x ＝ raise-one-Large-Commutative-Ring l
  eq-raise-one-is-one-Large-Commutative-Ring =
    eq-raise-one-is-one-Large-Ring (large-ring-Large-Commutative-Ring R)

  left-raise-unit-law-mul-Large-Commutative-Ring :
    {l1 l2 : Level} (y : type-Large-Commutative-Ring R l2) →
    mul-Large-Commutative-Ring R (raise-one-Large-Commutative-Ring l1) y ＝
    raise-Large-Commutative-Ring R l1 y
  left-raise-unit-law-mul-Large-Commutative-Ring =
    left-raise-unit-law-mul-Large-Ring (large-ring-Large-Commutative-Ring R)

  right-raise-unit-law-mul-Large-Commutative-Ring :
    {l1 l2 : Level} (x : type-Large-Commutative-Ring R l1) →
    mul-Large-Commutative-Ring R x (raise-one-Large-Commutative-Ring l2) ＝
    raise-Large-Commutative-Ring R l2 x
  right-raise-unit-law-mul-Large-Commutative-Ring =
    right-raise-unit-law-mul-Large-Ring (large-ring-Large-Commutative-Ring R)

  left-raise-unit-law-mul-Large-Commutative-Ring' :
    {l : Level} (y : type-Large-Commutative-Ring R l) →
    mul-Large-Commutative-Ring R (raise-one-Large-Commutative-Ring l) y ＝ y
  left-raise-unit-law-mul-Large-Commutative-Ring' =
    left-raise-unit-law-mul-Large-Ring' (large-ring-Large-Commutative-Ring R)

  right-raise-unit-law-mul-Large-Commutative-Ring' :
    {l : Level} (x : type-Large-Commutative-Ring R l) →
    mul-Large-Commutative-Ring R x (raise-one-Large-Commutative-Ring l) ＝ x
  right-raise-unit-law-mul-Large-Commutative-Ring' =
    right-raise-unit-law-mul-Large-Ring' (large-ring-Large-Commutative-Ring R)

  eq-left-is-one-law-mul-Large-Commutative-Ring :
    {l1 l2 : Level}
    (x : type-Large-Commutative-Ring R l1)
    (y : type-Large-Commutative-Ring R l2) →
    is-one-Large-Commutative-Ring x →
    mul-Large-Commutative-Ring R x y ＝ raise-Large-Commutative-Ring R l1 y
  eq-left-is-one-law-mul-Large-Commutative-Ring =
    eq-left-is-one-law-mul-Large-Ring (large-ring-Large-Commutative-Ring R)

  eq-right-is-one-law-mul-Large-Commutative-Ring :
    {l1 l2 : Level}
    (x : type-Large-Commutative-Ring R l1)
    (y : type-Large-Commutative-Ring R l2) →
    is-one-Large-Commutative-Ring y →
    mul-Large-Commutative-Ring R x y ＝ raise-Large-Commutative-Ring R l2 x
  eq-right-is-one-law-mul-Large-Commutative-Ring =
    eq-right-is-one-law-mul-Large-Ring (large-ring-Large-Commutative-Ring R)

  sim-left-is-one-law-mul-Large-Commutative-Ring :
    {l1 l2 : Level}
    (x : type-Large-Commutative-Ring R l1)
    (y : type-Large-Commutative-Ring R l2) →
    is-one-Large-Commutative-Ring x →
    sim-Large-Commutative-Ring R (mul-Large-Commutative-Ring R x y) y
  sim-left-is-one-law-mul-Large-Commutative-Ring =
    sim-left-is-one-law-mul-Large-Ring (large-ring-Large-Commutative-Ring R)

  sim-right-is-one-law-mul-Large-Commutative-Ring :
    {l1 l2 : Level}
    (x : type-Large-Commutative-Ring R l1)
    (y : type-Large-Commutative-Ring R l2) →
    is-one-Large-Commutative-Ring y →
    sim-Large-Commutative-Ring R (mul-Large-Commutative-Ring R x y) x
  sim-right-is-one-law-mul-Large-Commutative-Ring =
    sim-right-is-one-law-mul-Large-Ring (large-ring-Large-Commutative-Ring R)
```

### Zero laws of multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Commutative-Ring α β)
  where

  abstract
    left-is-zero-law-mul-Large-Commutative-Ring :
      {l1 l2 : Level}
      (x : type-Large-Commutative-Ring R l1)
      (y : type-Large-Commutative-Ring R l2) →
      is-zero-Large-Commutative-Ring R x →
      is-zero-Large-Commutative-Ring R (mul-Large-Commutative-Ring R x y)
    left-is-zero-law-mul-Large-Commutative-Ring =
      left-is-zero-law-mul-Large-Ring (large-ring-Large-Commutative-Ring R)

    right-is-zero-law-mul-Large-Commutative-Ring :
      {l1 l2 : Level}
      (x : type-Large-Commutative-Ring R l1)
      (y : type-Large-Commutative-Ring R l2) →
      is-zero-Large-Commutative-Ring R y →
      is-zero-Large-Commutative-Ring R (mul-Large-Commutative-Ring R x y)
    right-is-zero-law-mul-Large-Commutative-Ring =
      right-is-zero-law-mul-Large-Ring (large-ring-Large-Commutative-Ring R)

    sim-left-zero-law-mul-Large-Commutative-Ring :
      {l : Level} (x : type-Large-Commutative-Ring R l) →
      is-zero-Large-Commutative-Ring R
        ( mul-Large-Commutative-Ring R (zero-Large-Commutative-Ring R) x)
    sim-left-zero-law-mul-Large-Commutative-Ring =
      sim-left-zero-law-mul-Large-Ring (large-ring-Large-Commutative-Ring R)

    sim-right-zero-law-mul-Large-Commutative-Ring :
      {l : Level} (x : type-Large-Commutative-Ring R l) →
      is-zero-Large-Commutative-Ring R
        ( mul-Large-Commutative-Ring R x (zero-Large-Commutative-Ring R))
    sim-right-zero-law-mul-Large-Commutative-Ring =
      sim-right-zero-law-mul-Large-Ring (large-ring-Large-Commutative-Ring R)

    left-raise-zero-law-mul-Large-Commutative-Ring :
      {l1 l2 : Level} (y : type-Large-Commutative-Ring R l1) →
      mul-Large-Commutative-Ring R (raise-zero-Large-Commutative-Ring R l2) y ＝
      raise-zero-Large-Commutative-Ring R (l1 ⊔ l2)
    left-raise-zero-law-mul-Large-Commutative-Ring =
      left-raise-zero-law-mul-Large-Ring (large-ring-Large-Commutative-Ring R)

    right-raise-zero-law-mul-Large-Commutative-Ring :
      {l1 l2 : Level} (x : type-Large-Commutative-Ring R l1) →
      mul-Large-Commutative-Ring R x (raise-zero-Large-Commutative-Ring R l2) ＝
      raise-zero-Large-Commutative-Ring R (l1 ⊔ l2)
    right-raise-zero-law-mul-Large-Commutative-Ring =
      right-raise-zero-law-mul-Large-Ring (large-ring-Large-Commutative-Ring R)
```

### Negative laws of multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  {l1 l2 : Level}
  (x : type-Large-Commutative-Ring R l1)
  (y : type-Large-Commutative-Ring R l2)
  where

  abstract
    left-negative-law-mul-Large-Commutative-Ring :
      mul-Large-Commutative-Ring R (neg-Large-Commutative-Ring R x) y ＝
      neg-Large-Commutative-Ring R (mul-Large-Commutative-Ring R x y)
    left-negative-law-mul-Large-Commutative-Ring =
      left-negative-law-mul-Large-Ring (large-ring-Large-Commutative-Ring R) x y

    right-negative-law-mul-Large-Commutative-Ring :
      mul-Large-Commutative-Ring R x (neg-Large-Commutative-Ring R y) ＝
      neg-Large-Commutative-Ring R (mul-Large-Commutative-Ring R x y)
    right-negative-law-mul-Large-Commutative-Ring =
      right-negative-law-mul-Large-Ring
        ( large-ring-Large-Commutative-Ring R)
        ( x)
        ( y)
```

### Multiplication by negative one is negation

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  where

  neg-one-Large-Commutative-Ring : type-Large-Commutative-Ring R lzero
  neg-one-Large-Commutative-Ring =
    neg-one-Large-Ring (large-ring-Large-Commutative-Ring R)

  abstract
    left-neg-one-law-mul-Large-Commutative-Ring :
      {l : Level} (x : type-Large-Commutative-Ring R l) →
      mul-Large-Commutative-Ring R neg-one-Large-Commutative-Ring x ＝
      neg-Large-Commutative-Ring R x
    left-neg-one-law-mul-Large-Commutative-Ring =
      left-neg-one-law-mul-Large-Ring (large-ring-Large-Commutative-Ring R)

    right-neg-one-law-mul-Large-Commutative-Ring :
      {l : Level} (x : type-Large-Commutative-Ring R l) →
      mul-Large-Commutative-Ring R x neg-one-Large-Commutative-Ring ＝
      neg-Large-Commutative-Ring R x
    right-neg-one-law-mul-Large-Commutative-Ring =
      right-neg-one-law-mul-Large-Ring (large-ring-Large-Commutative-Ring R)
```

### Distributive laws of multiplication over addition and subtraction

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  {l1 l2 l3 : Level}
  (x : type-Large-Commutative-Ring R l1)
  (y : type-Large-Commutative-Ring R l2)
  (z : type-Large-Commutative-Ring R l3)
  where

  abstract
    left-distributive-mul-add-Large-Commutative-Ring :
      mul-Large-Commutative-Ring R x (add-Large-Commutative-Ring R y z) ＝
      add-Large-Commutative-Ring R
        ( mul-Large-Commutative-Ring R x y)
        ( mul-Large-Commutative-Ring R x z)
    left-distributive-mul-add-Large-Commutative-Ring =
      left-distributive-mul-add-Large-Ring
        ( large-ring-Large-Commutative-Ring R)
        ( x)
        ( y)
        ( z)

    right-distributive-mul-add-Large-Commutative-Ring :
      mul-Large-Commutative-Ring R (add-Large-Commutative-Ring R x y) z ＝
      add-Large-Commutative-Ring R
        ( mul-Large-Commutative-Ring R x z)
        ( mul-Large-Commutative-Ring R y z)
    right-distributive-mul-add-Large-Commutative-Ring =
      right-distributive-mul-add-Large-Ring
        ( large-ring-Large-Commutative-Ring R)
        ( x)
        ( y)
        ( z)

    left-distributive-mul-diff-Large-Commutative-Ring :
      mul-Large-Commutative-Ring R x (diff-Large-Commutative-Ring R y z) ＝
      diff-Large-Commutative-Ring R
        ( mul-Large-Commutative-Ring R x y)
        ( mul-Large-Commutative-Ring R x z)
    left-distributive-mul-diff-Large-Commutative-Ring =
      left-distributive-mul-diff-Large-Ring
        ( large-ring-Large-Commutative-Ring R)
        ( x)
        ( y)
        ( z)

    right-distributive-mul-diff-Large-Commutative-Ring :
      mul-Large-Commutative-Ring R (diff-Large-Commutative-Ring R x y) z ＝
      diff-Large-Commutative-Ring R
        ( mul-Large-Commutative-Ring R x z)
        ( mul-Large-Commutative-Ring R y z)
    right-distributive-mul-diff-Large-Commutative-Ring =
      right-distributive-mul-diff-Large-Ring
        ( large-ring-Large-Commutative-Ring R)
        ( x)
        ( y)
        ( z)
```

### Swapping laws of multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  {l1 l2 l3 : Level}
  (x : type-Large-Commutative-Ring R l1)
  (y : type-Large-Commutative-Ring R l2)
  (z : type-Large-Commutative-Ring R l3)
  where

  abstract
    left-swap-mul-Large-Commutative-Ring :
      mul-Large-Commutative-Ring R x (mul-Large-Commutative-Ring R y z) ＝
      mul-Large-Commutative-Ring R y (mul-Large-Commutative-Ring R x z)
    left-swap-mul-Large-Commutative-Ring =
      left-swap-mul-Large-Commutative-Monoid
        ( large-commutative-monoid-mul-Large-Commutative-Ring R)
        ( x)
        ( y)
        ( z)

    right-swap-mul-Large-Commutative-Ring :
      mul-Large-Commutative-Ring R (mul-Large-Commutative-Ring R x y) z ＝
      mul-Large-Commutative-Ring R (mul-Large-Commutative-Ring R x z) y
    right-swap-mul-Large-Commutative-Ring =
      right-swap-mul-Large-Commutative-Monoid
        ( large-commutative-monoid-mul-Large-Commutative-Ring R)
        ( x)
        ( y)
        ( z)
```

### Interchange laws of multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  {l1 l2 l3 l4 : Level}
  (x : type-Large-Commutative-Ring R l1)
  (y : type-Large-Commutative-Ring R l2)
  (z : type-Large-Commutative-Ring R l3)
  (w : type-Large-Commutative-Ring R l4)
  where

  abstract
    interchange-mul-mul-Large-Commutative-Ring :
      mul-Large-Commutative-Ring R
        ( mul-Large-Commutative-Ring R x y)
        ( mul-Large-Commutative-Ring R z w) ＝
      mul-Large-Commutative-Ring R
        ( mul-Large-Commutative-Ring R x z)
        ( mul-Large-Commutative-Ring R y w)
    interchange-mul-mul-Large-Commutative-Ring =
      interchange-mul-mul-Large-Commutative-Monoid
        ( large-commutative-monoid-mul-Large-Commutative-Ring R)
        ( x)
        ( y)
        ( z)
        ( w)
```

### The raise operation is a commutative ring homomorphism

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β) (l1 l2 : Level)
  where

  hom-raise-Large-Commutative-Ring :
    hom-Commutative-Ring
      ( commutative-ring-Large-Commutative-Ring R l1)
      ( commutative-ring-Large-Commutative-Ring R (l1 ⊔ l2))
  hom-raise-Large-Commutative-Ring =
    hom-raise-Large-Ring (large-ring-Large-Commutative-Ring R) l1 l2
```
