# Large abelian groups

```agda
module group-theory.large-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.automorphisms
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

open import group-theory.abelian-groups
open import group-theory.conjugation-large-groups
open import group-theory.groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.large-commutative-monoids
open import group-theory.large-groups
open import group-theory.large-monoids
```

</details>

## Idea

A {{#concept "large abelian group" Agda=Large-Ab}} is a
[large group](group-theory.large-groups.md) whose binary operation is
commutative.

## Definition

```agda
record Large-Ab (α : Level → Level) (β : Level → Level → Level) : UUω where

  constructor
    make-Large-Ab

  field
    large-group-Large-Ab : Large-Group α β

  cumulative-large-set-Large-Ab : Cumulative-Large-Set α β
  cumulative-large-set-Large-Ab =
    cumulative-large-set-Large-Group large-group-Large-Ab

  set-Large-Ab : (l : Level) → Set (α l)
  set-Large-Ab = set-Large-Group large-group-Large-Ab

  type-Large-Ab : (l : Level) → UU (α l)
  type-Large-Ab = type-Large-Group large-group-Large-Ab

  add-Large-Ab :
    {l1 l2 : Level} → type-Large-Ab l1 → type-Large-Ab l2 →
    type-Large-Ab (l1 ⊔ l2)
  add-Large-Ab = mul-Large-Group large-group-Large-Ab

  add-Large-Ab' :
    {l1 l2 : Level} → type-Large-Ab l1 → type-Large-Ab l2 →
    type-Large-Ab (l1 ⊔ l2)
  add-Large-Ab' x y = add-Large-Ab y x

  ap-add-Large-Ab :
    {l1 l2 : Level} {x x' : type-Large-Ab l1} → x ＝ x' →
    {y y' : type-Large-Ab l2} → y ＝ y' →
    add-Large-Ab x y ＝ add-Large-Ab x' y'
  ap-add-Large-Ab =
    ap-mul-Large-Group large-group-Large-Ab

  field
    commutative-add-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab l1) (y : type-Large-Ab l2) →
      add-Large-Ab x y ＝ add-Large-Ab y x

  neg-Large-Ab : {l : Level} → type-Large-Ab l → type-Large-Ab l
  neg-Large-Ab = inv-Large-Group large-group-Large-Ab

  large-monoid-Large-Ab : Large-Monoid α β
  large-monoid-Large-Ab =
    large-monoid-Large-Group large-group-Large-Ab

  large-commutative-monoid-Large-Ab : Large-Commutative-Monoid α β
  large-commutative-monoid-Large-Ab =
    λ where
      .large-monoid-Large-Commutative-Monoid →
        large-monoid-Large-Ab
      .commutative-mul-Large-Commutative-Monoid →
        commutative-add-Large-Ab

open Large-Ab public
```

## Properties

### Similarity

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (G : Large-Ab α β)
  where

  large-similarity-relation-Large-Ab :
    Large-Similarity-Relation β (type-Large-Ab G)
  large-similarity-relation-Large-Ab =
    large-similarity-relation-Large-Group (large-group-Large-Ab G)

  sim-prop-Large-Ab :
    Large-Relation-Prop β (type-Large-Ab G)
  sim-prop-Large-Ab =
    sim-prop-Large-Group (large-group-Large-Ab G)

  sim-Large-Ab : Large-Relation β (type-Large-Ab G)
  sim-Large-Ab = sim-Large-Group (large-group-Large-Ab G)

  refl-sim-Large-Ab :
    is-reflexive-Large-Relation (type-Large-Ab G) sim-Large-Ab
  refl-sim-Large-Ab =
    refl-sim-Large-Group (large-group-Large-Ab G)

  symmetric-sim-Large-Ab :
    is-symmetric-Large-Relation (type-Large-Ab G) sim-Large-Ab
  symmetric-sim-Large-Ab =
    symmetric-sim-Large-Group (large-group-Large-Ab G)

  transitive-sim-Large-Ab :
    is-transitive-Large-Relation (type-Large-Ab G) sim-Large-Ab
  transitive-sim-Large-Ab =
    transitive-sim-Large-Group (large-group-Large-Ab G)

  sim-eq-Large-Ab :
    {l : Level} {x y : type-Large-Ab G l} → x ＝ y → sim-Large-Ab x y
  sim-eq-Large-Ab = sim-eq-Large-Group (large-group-Large-Ab G)

  eq-sim-Large-Ab :
    {l : Level} (x y : type-Large-Ab G l) → sim-Large-Ab x y → x ＝ y
  eq-sim-Large-Ab = eq-sim-Large-Group (large-group-Large-Ab G)
```

### Similarity reasoning on large abelian groups

```agda
module
  similarity-reasoning-Large-Ab
    {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  open similarity-reasoning-Large-Group (large-group-Large-Ab G) public
```

### Raising universe levels

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (G : Large-Ab α β)
  where

  raise-Large-Ab :
    {l0 : Level} (l : Level) →
    type-Large-Ab G l0 → type-Large-Ab G (l0 ⊔ l)
  raise-Large-Ab = raise-Large-Group (large-group-Large-Ab G)

  sim-raise-Large-Ab :
    {l0 : Level} (l : Level) (x : type-Large-Ab G l0) →
    sim-Large-Ab G x (raise-Large-Ab l x)
  sim-raise-Large-Ab =
    sim-raise-Large-Group (large-group-Large-Ab G)

  sim-raise-Large-Ab' :
    {l0 : Level} (l : Level) (x : type-Large-Ab G l0) →
    sim-Large-Ab G (raise-Large-Ab l x) x
  sim-raise-Large-Ab' =
    sim-raise-Large-Group' (large-group-Large-Ab G)

  eq-raise-Large-Ab :
    {l : Level} (x : type-Large-Ab G l) → raise-Large-Ab l x ＝ x
  eq-raise-Large-Ab =
    eq-raise-Large-Group (large-group-Large-Ab G)

  eq-raise-leq-level-Large-Ab :
    (l1 : Level) {l2 : Level} (x : type-Large-Ab G (l1 ⊔ l2)) →
    raise-Large-Ab l2 x ＝ x
  eq-raise-leq-level-Large-Ab =
    eq-raise-leq-level-Large-Group (large-group-Large-Ab G)

  is-emb-raise-Large-Ab :
    (l1 l2 : Level) → is-emb (raise-Large-Ab {l1} l2)
  is-emb-raise-Large-Ab =
    is-emb-raise-Large-Group (large-group-Large-Ab G)

  emb-raise-Large-Ab :
    (l1 l2 : Level) → type-Large-Ab G l1 ↪ type-Large-Ab G (l1 ⊔ l2)
  emb-raise-Large-Ab =
    emb-raise-Large-Group (large-group-Large-Ab G)

  raise-raise-Large-Ab :
    {l0 l1 l2 : Level} (x : type-Large-Ab G l0) →
    raise-Large-Ab l1 (raise-Large-Ab l2 x) ＝
    raise-Large-Ab (l1 ⊔ l2) x
  raise-raise-Large-Ab =
    raise-raise-Large-Group (large-group-Large-Ab G)

  eq-raise-sim-Large-Ab :
    {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
    sim-Large-Ab G x y → raise-Large-Ab l2 x ＝ raise-Large-Ab l1 y
  eq-raise-sim-Large-Ab =
    eq-raise-sim-Large-Group (large-group-Large-Ab G)

  sim-eq-raise-Large-Ab :
    {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
    raise-Large-Ab l2 x ＝ raise-Large-Ab l1 y → sim-Large-Ab G x y
  sim-eq-raise-Large-Ab =
    sim-eq-raise-Large-Group (large-group-Large-Ab G)

  eq-raise-iff-sim-Large-Ab :
    {l1 l2 : Level} →
    (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
    ( sim-Large-Ab G x y ↔
      ( raise-Large-Ab l2 x ＝ raise-Large-Ab l1 y))
  eq-raise-iff-sim-Large-Ab =
    eq-raise-iff-sim-Large-Group (large-group-Large-Ab G)

  eq-raise-sim-Large-Ab' :
    {l1 l2 : Level}
    (x : type-Large-Ab G (l1 ⊔ l2)) (y : type-Large-Ab G l2) →
    sim-Large-Ab G x y → x ＝ raise-Large-Ab l1 y
  eq-raise-sim-Large-Ab' =
    eq-raise-sim-Large-Group' (large-group-Large-Ab G)
```

### Similarity preservation of addition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  sim-preserving-binary-operator-add-Large-Ab :
    sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Ab G)
  sim-preserving-binary-operator-add-Large-Ab =
    sim-preserving-binary-operator-mul-Large-Group (large-group-Large-Ab G)

  preserves-sim-add-Large-Ab :
    preserves-sim-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Ab G)
      ( add-Large-Ab G)
  preserves-sim-add-Large-Ab =
    preserves-sim-mul-Large-Group (large-group-Large-Ab G)

  sim-preserving-map-left-add-Large-Ab :
    {l : Level} (x : type-Large-Ab G l) →
    sim-preserving-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Ab G)
  sim-preserving-map-left-add-Large-Ab =
    sim-preserving-map-left-mul-Large-Group (large-group-Large-Ab G)

  preserves-sim-left-add-Large-Ab :
    {l : Level} (x : type-Large-Ab G l) →
    preserves-sim-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Ab G)
      ( add-Large-Ab G x)
  preserves-sim-left-add-Large-Ab =
    preserves-sim-left-mul-Large-Group (large-group-Large-Ab G)

  sim-preserving-map-right-add-Large-Ab :
    {l : Level} (y : type-Large-Ab G l) →
    sim-preserving-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Ab G)
  sim-preserving-map-right-add-Large-Ab =
    sim-preserving-map-right-mul-Large-Group
      ( large-group-Large-Ab G)

  preserves-sim-right-add-Large-Ab :
    {l : Level} (y : type-Large-Ab G l) →
    preserves-sim-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Ab G)
      ( add-Large-Ab' G y)
  preserves-sim-right-add-Large-Ab =
    preserves-sim-right-mul-Large-Group (large-group-Large-Ab G)
```

### Raising universe levels in multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    add-raise-right-Large-Ab :
      {l1 l2 : Level} (l3 : Level) →
      (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      add-Large-Ab G x (raise-Large-Ab G l3 y) ＝
      raise-Large-Ab G l3 (add-Large-Ab G x y)
    add-raise-right-Large-Ab =
      mul-raise-right-Large-Group (large-group-Large-Ab G)

    add-raise-left-Large-Ab :
      {l1 l2 : Level} (l3 : Level) →
      (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      add-Large-Ab G (raise-Large-Ab G l3 x) y ＝
      raise-Large-Ab G l3 (add-Large-Ab G x y)
    add-raise-left-Large-Ab =
      mul-raise-left-Large-Group (large-group-Large-Ab G)

    add-raise-raise-Large-Ab :
      {l1 l2 : Level} (l3 l4 : Level) →
      (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      add-Large-Ab G
        ( raise-Large-Ab G l3 x)
        ( raise-Large-Ab G l4 y) ＝
      raise-Large-Ab G (l3 ⊔ l4) (add-Large-Ab G x y)
    add-raise-raise-Large-Ab =
      mul-raise-raise-Large-Group (large-group-Large-Ab G)
```

### The negation operation preserves similarity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  sim-preserving-endomap-neg-Large-Ab :
    sim-preserving-endomap-Cumulative-Large-Set
      ( id)
      ( cumulative-large-set-Large-Ab G)
  sim-preserving-endomap-neg-Large-Ab =
    sim-preserving-endomap-inv-Large-Group (large-group-Large-Ab G)

  preserves-sim-neg-Large-Ab :
    preserves-sim-endomap-Cumulative-Large-Set
      ( id)
      ( cumulative-large-set-Large-Ab G)
      ( neg-Large-Ab G)
  preserves-sim-neg-Large-Ab =
    preserves-sim-inv-Large-Group (large-group-Large-Ab G)
```

### Semigroup laws of addition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  associative-add-Large-Ab :
    {l1 l2 l3 : Level}
    (x : type-Large-Ab G l1)
    (y : type-Large-Ab G l2)
    (z : type-Large-Ab G l3) →
    add-Large-Ab G (add-Large-Ab G x y) z ＝
    add-Large-Ab G x (add-Large-Ab G y z)
  associative-add-Large-Ab =
    associative-mul-Large-Group (large-group-Large-Ab G)
```

### Monoid laws of addition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  zero-Large-Ab : type-Large-Ab G lzero
  zero-Large-Ab = unit-Large-Group (large-group-Large-Ab G)

  raise-zero-Large-Ab : (l : Level) → type-Large-Ab G l
  raise-zero-Large-Ab = raise-unit-Large-Group (large-group-Large-Ab G)

  raise-zero-lzero-Large-Ab :
    raise-zero-Large-Ab lzero ＝ zero-Large-Ab
  raise-zero-lzero-Large-Ab =
    raise-unit-lzero-Large-Group (large-group-Large-Ab G)

  is-zero-prop-Large-Ab : {l : Level} → type-Large-Ab G l → Prop (β l lzero)
  is-zero-prop-Large-Ab = is-unit-prop-Large-Group (large-group-Large-Ab G)

  is-zero-Large-Ab : {l : Level} → type-Large-Ab G l → UU (β l lzero)
  is-zero-Large-Ab x = type-Prop (is-zero-prop-Large-Ab x)

  is-zero-zero-Large-Ab : is-zero-Large-Ab zero-Large-Ab
  is-zero-zero-Large-Ab =
    is-unit-unit-Large-Group (large-group-Large-Ab G)

  is-zero-raise-zero-Large-Ab :
    (l : Level) → is-zero-Large-Ab (raise-zero-Large-Ab l)
  is-zero-raise-zero-Large-Ab =
    is-unit-raise-unit-Large-Group (large-group-Large-Ab G)

  eq-raise-zero-is-zero-Large-Ab :
    {l : Level} (x : type-Large-Ab G l) →
    is-zero-Large-Ab x → x ＝ raise-zero-Large-Ab l
  eq-raise-zero-is-zero-Large-Ab =
    eq-raise-unit-is-unit-Large-Group (large-group-Large-Ab G)

  left-unit-law-add-Large-Ab :
    {l : Level} (x : type-Large-Ab G l) →
    add-Large-Ab G zero-Large-Ab x ＝ x
  left-unit-law-add-Large-Ab =
    left-unit-law-mul-Large-Group (large-group-Large-Ab G)

  right-unit-law-add-Large-Ab :
    {l : Level} (x : type-Large-Ab G l) →
    add-Large-Ab G x zero-Large-Ab ＝ x
  right-unit-law-add-Large-Ab =
    right-unit-law-mul-Large-Group (large-group-Large-Ab G)

  left-raise-unit-law-add-Large-Ab :
    {l1 l2 : Level} (y : type-Large-Ab G l2) →
    add-Large-Ab G (raise-zero-Large-Ab l1) y ＝ raise-Large-Ab G l1 y
  left-raise-unit-law-add-Large-Ab =
    left-raise-unit-law-mul-Large-Group (large-group-Large-Ab G)

  right-raise-unit-law-add-Large-Ab :
    {l1 l2 : Level} (x : type-Large-Ab G l1) →
    add-Large-Ab G x (raise-zero-Large-Ab l2) ＝ raise-Large-Ab G l2 x
  right-raise-unit-law-add-Large-Ab =
    right-raise-unit-law-mul-Large-Group (large-group-Large-Ab G)

  eq-left-is-zero-law-add-Large-Ab :
    {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
    is-zero-Large-Ab x → add-Large-Ab G x y ＝ raise-Large-Ab G l1 y
  eq-left-is-zero-law-add-Large-Ab =
    eq-left-is-unit-law-mul-Large-Group (large-group-Large-Ab G)

  eq-right-is-zero-law-add-Large-Ab :
    {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
    is-zero-Large-Ab y → add-Large-Ab G x y ＝ raise-Large-Ab G l2 x
  eq-right-is-zero-law-add-Large-Ab =
    eq-right-is-unit-law-mul-Large-Group (large-group-Large-Ab G)

  sim-left-is-zero-law-add-Large-Ab :
    {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
    is-zero-Large-Ab x → sim-Large-Ab G (add-Large-Ab G x y) y
  sim-left-is-zero-law-add-Large-Ab =
    sim-left-is-unit-law-mul-Large-Group (large-group-Large-Ab G)

  sim-right-is-zero-law-add-Large-Ab :
    {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
    is-zero-Large-Ab y → sim-Large-Ab G (add-Large-Ab G x y) x
  sim-right-is-zero-law-add-Large-Ab =
    sim-right-is-unit-law-mul-Large-Group (large-group-Large-Ab G)
```

### Inverse laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    sim-left-inverse-law-add-Large-Ab :
      {l : Level} (x : type-Large-Ab G l) →
      is-zero-Large-Ab G (add-Large-Ab G (neg-Large-Ab G x) x)
    sim-left-inverse-law-add-Large-Ab =
      sim-left-inverse-law-mul-Large-Group (large-group-Large-Ab G)

    sim-right-inverse-law-add-Large-Ab :
      {l : Level} (x : type-Large-Ab G l) →
      is-zero-Large-Ab G (add-Large-Ab G x (neg-Large-Ab G x))
    sim-right-inverse-law-add-Large-Ab =
      sim-right-inverse-law-mul-Large-Group (large-group-Large-Ab G)

    eq-left-inverse-law-add-Large-Ab :
      {l : Level} (x : type-Large-Ab G l) →
      add-Large-Ab G (neg-Large-Ab G x) x ＝ raise-zero-Large-Ab G l
    eq-left-inverse-law-add-Large-Ab =
      eq-left-inverse-law-mul-Large-Group (large-group-Large-Ab G)

    eq-right-inverse-law-add-Large-Ab :
      {l : Level} (x : type-Large-Ab G l) →
      add-Large-Ab G x (neg-Large-Ab G x) ＝ raise-zero-Large-Ab G l
    eq-right-inverse-law-add-Large-Ab =
      eq-right-inverse-law-mul-Large-Group (large-group-Large-Ab G)
```

### Cancellation laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2)
  where

  abstract
    sim-cancel-left-diff-add-Large-Ab :
      sim-Large-Ab G
        ( add-Large-Ab G (neg-Large-Ab G x) (add-Large-Ab G x y))
        ( y)
    sim-cancel-left-diff-add-Large-Ab =
      sim-cancel-left-div-mul-Large-Group (large-group-Large-Ab G) x y

    sim-cancel-left-add-diff-Large-Ab :
      sim-Large-Ab G
        ( add-Large-Ab G x (add-Large-Ab G (neg-Large-Ab G x) y))
        ( y)
    sim-cancel-left-add-diff-Large-Ab =
      sim-cancel-left-mul-div-Large-Group (large-group-Large-Ab G) x y

    sim-cancel-right-diff-add-Large-Ab :
      sim-Large-Ab G
        ( add-Large-Ab G (add-Large-Ab G y (neg-Large-Ab G x)) x)
        ( y)
    sim-cancel-right-diff-add-Large-Ab =
      sim-cancel-right-div-mul-Large-Group (large-group-Large-Ab G) x y

    sim-cancel-right-add-diff-Large-Ab :
      sim-Large-Ab G
        ( add-Large-Ab G (add-Large-Ab G y x) (neg-Large-Ab G x))
        ( y)
    sim-cancel-right-add-diff-Large-Ab =
      sim-cancel-right-mul-div-Large-Group (large-group-Large-Ab G) x y

    eq-cancel-left-diff-add-Large-Ab :
      add-Large-Ab G (neg-Large-Ab G x) (add-Large-Ab G x y) ＝
      raise-Large-Ab G l1 y
    eq-cancel-left-diff-add-Large-Ab =
      eq-cancel-left-div-mul-Large-Group (large-group-Large-Ab G) x y

    eq-cancel-left-add-diff-Large-Ab :
      add-Large-Ab G x (add-Large-Ab G (neg-Large-Ab G x) y) ＝
      raise-Large-Ab G l1 y
    eq-cancel-left-add-diff-Large-Ab =
      eq-cancel-left-mul-div-Large-Group (large-group-Large-Ab G) x y

    eq-cancel-right-diff-add-Large-Ab :
      add-Large-Ab G (add-Large-Ab G y (neg-Large-Ab G x)) x ＝
      raise-Large-Ab G l1 y
    eq-cancel-right-diff-add-Large-Ab =
      eq-cancel-right-div-mul-Large-Group (large-group-Large-Ab G) x y

    eq-cancel-right-add-diff-Large-Ab :
      add-Large-Ab G (add-Large-Ab G y x) (neg-Large-Ab G x) ＝
      raise-Large-Ab G l1 y
    eq-cancel-right-add-diff-Large-Ab =
      eq-cancel-right-mul-div-Large-Group (large-group-Large-Ab G) x y
```

### Uniqueness of inverses

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    unique-left-neg-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      is-zero-Large-Ab G (add-Large-Ab G x y) →
      sim-Large-Ab G x (neg-Large-Ab G y)
    unique-left-neg-Large-Ab =
      unique-left-inv-Large-Group (large-group-Large-Ab G)

    unique-right-neg-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      is-zero-Large-Ab G (add-Large-Ab G x y) →
      sim-Large-Ab G y (neg-Large-Ab G x)
    unique-right-neg-Large-Ab =
      unique-right-inv-Large-Group (large-group-Large-Ab G)
```

### The negation of zero is zero

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    neg-is-zero-Large-Ab :
      {l : Level} (x : type-Large-Ab G l) →
      is-zero-Large-Ab G x → is-zero-Large-Ab G (neg-Large-Ab G x)
    neg-is-zero-Large-Ab = inv-is-unit-Large-Group (large-group-Large-Ab G)

    neg-zero-Large-Ab :
      neg-Large-Ab G (zero-Large-Ab G) ＝ zero-Large-Ab G
    neg-zero-Large-Ab = inv-unit-Large-Group (large-group-Large-Ab G)

    neg-raise-zero-Large-Ab :
      (l : Level) →
      neg-Large-Ab G (raise-zero-Large-Ab G l) ＝ raise-zero-Large-Ab G l
    neg-raise-zero-Large-Ab =
      inv-raise-unit-Large-Group (large-group-Large-Ab G)
```

### Distributivity of negation over addition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    distributive-neg-add-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      neg-Large-Ab G (add-Large-Ab G x y) ＝
      add-Large-Ab G (neg-Large-Ab G x) (neg-Large-Ab G y)
    distributive-neg-add-Large-Ab x y =
      ( distributive-inv-mul-Large-Group (large-group-Large-Ab G) x y) ∙
      ( commutative-add-Large-Ab G (neg-Large-Ab G y) (neg-Large-Ab G x))
```

### Negation is an involution

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    neg-neg-Large-Ab :
      {l : Level} (x : type-Large-Ab G l) →
      neg-Large-Ab G (neg-Large-Ab G x) ＝ x
    neg-neg-Large-Ab = inv-inv-Large-Group (large-group-Large-Ab G)
```

### Right addition reflects similarity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  {l1 l2 l3 : Level}
  (x : type-Large-Ab G l1)
  (y : type-Large-Ab G l2)
  (z : type-Large-Ab G l3)
  where

  abstract
    reflects-sim-right-add-Large-Ab :
      sim-Large-Ab G (add-Large-Ab G x z) (add-Large-Ab G y z) →
      sim-Large-Ab G x y
    reflects-sim-right-add-Large-Ab =
      reflects-sim-right-mul-Large-Group (large-group-Large-Ab G) x y z
```

### Left addition reflects similarity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  {l1 l2 l3 : Level}
  (x : type-Large-Ab G l1)
  (y : type-Large-Ab G l2)
  (z : type-Large-Ab G l3)
  where

  abstract
    reflects-sim-left-add-Large-Ab :
      sim-Large-Ab G (add-Large-Ab G x y) (add-Large-Ab G x z) →
      sim-Large-Ab G y z
    reflects-sim-left-add-Large-Ab =
      reflects-sim-left-mul-Large-Group (large-group-Large-Ab G) x y z
```

### Left addition in a large abelian group is an embedding

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  {l1 : Level} (l2 : Level) (x : type-Large-Ab G l1)
  where

  abstract
    is-emb-left-add-Large-Ab :
      is-emb (add-Large-Ab G {l2 = l2} x)
    is-emb-left-add-Large-Ab =
      is-emb-left-mul-Large-Group (large-group-Large-Ab G) l2 x
```

### Right addition in a large abelian group is an embedding

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  {l1 : Level} (l2 : Level) (x : type-Large-Ab G l1)
  where

  abstract
    is-emb-right-add-Large-Ab :
      is-emb (add-Large-Ab' G {l2 = l2} x)
    is-emb-right-add-Large-Ab =
      is-emb-right-mul-Large-Group (large-group-Large-Ab G) l2 x
```

### Small abelian groups from large abelian groups

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  group-Large-Ab : (l : Level) → Group (α l)
  group-Large-Ab = group-Large-Group (large-group-Large-Ab G)

  ab-Large-Ab : (l : Level) → Ab (α l)
  ab-Large-Ab l =
    ( group-Large-Ab l ,
      commutative-add-Large-Ab G)
```

### The raise operation is an abelian group homomorphism

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  hom-raise-Large-Ab :
    (l1 l2 : Level) → hom-Ab (ab-Large-Ab G l1) (ab-Large-Ab G (l1 ⊔ l2))
  hom-raise-Large-Ab = hom-raise-Large-Group (large-group-Large-Ab G)
```

### `x + x ＝ x` if and only if `x` is zero

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    is-zero-is-idempotent-Large-Ab :
      {l : Level} (x : type-Large-Ab G l) →
      add-Large-Ab G x x ＝ x → is-zero-Large-Ab G x
    is-zero-is-idempotent-Large-Ab =
      is-unit-is-idempotent-Large-Group (large-group-Large-Ab G)

    eq-raise-zero-is-idempotent-Large-Ab :
      {l : Level} (x : type-Large-Ab G l) →
      add-Large-Ab G x x ＝ x → x ＝ raise-zero-Large-Ab G l
    eq-raise-zero-is-idempotent-Large-Ab =
      eq-raise-unit-is-idempotent-Large-Group (large-group-Large-Ab G)

    is-idempotent-is-zero-Large-Ab :
      {l : Level} (x : type-Large-Ab G l) →
      is-zero-Large-Ab G x → add-Large-Ab G x x ＝ x
    is-idempotent-is-zero-Large-Ab =
      is-idempotent-mul-is-unit-Large-Group (large-group-Large-Ab G)
```

### Swapping laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  {l1 l2 l3 : Level}
  (x : type-Large-Ab G l1)
  (y : type-Large-Ab G l2)
  (z : type-Large-Ab G l3)
  where

  abstract
    left-swap-add-Large-Ab :
      add-Large-Ab G x (add-Large-Ab G y z) ＝
      add-Large-Ab G y (add-Large-Ab G x z)
    left-swap-add-Large-Ab =
      left-swap-mul-Large-Commutative-Monoid
        ( large-commutative-monoid-Large-Ab G)
        ( x)
        ( y)
        ( z)

    right-swap-add-Large-Ab :
      add-Large-Ab G (add-Large-Ab G x y) z ＝
      add-Large-Ab G (add-Large-Ab G x z) y
    right-swap-add-Large-Ab =
      right-swap-mul-Large-Commutative-Monoid
        ( large-commutative-monoid-Large-Ab G)
        ( x)
        ( y)
        ( z)
```

### Conjugation in large abelian groups is the identity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  (let _+G_ = add-Large-Ab G)
  (let neg-G = neg-Large-Ab G)
  where

  left-conjugation-Large-Ab :
    {l1 l2 : Level} →
    type-Large-Ab G l1 → type-Large-Ab G l2 → type-Large-Ab G (l1 ⊔ l2)
  left-conjugation-Large-Ab =
    left-conjugation-Large-Group (large-group-Large-Ab G)

  right-conjugation-Large-Ab :
    {l1 l2 : Level} →
    type-Large-Ab G l1 → type-Large-Ab G l2 → type-Large-Ab G (l1 ⊔ l2)
  right-conjugation-Large-Ab =
    right-conjugation-Large-Group (large-group-Large-Ab G)

  abstract
    eq-left-right-conjugation-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      left-conjugation-Large-Ab x y ＝ right-conjugation-Large-Ab x y
    eq-left-right-conjugation-Large-Ab =
      eq-left-right-conjugation-Large-Group (large-group-Large-Ab G)

    cancel-left-conjugation-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      sim-Large-Ab G (left-conjugation-Large-Ab x y) y
    cancel-left-conjugation-Large-Ab x y =
      tr
        ( λ z → sim-Large-Ab G z y)
        ( right-swap-add-Large-Ab G x (neg-G x) y)
        ( sim-left-is-zero-law-add-Large-Ab G
          ( x +G neg-G x)
          ( y)
          ( sim-right-inverse-law-add-Large-Ab G x))

    cancel-right-conjugation-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      sim-Large-Ab G (right-conjugation-Large-Ab x y) y
    cancel-right-conjugation-Large-Ab x y =
      tr
        ( λ z → sim-Large-Ab G z y)
        ( eq-left-right-conjugation-Large-Ab x y)
        ( cancel-left-conjugation-Large-Ab x y)
```

### Interchange laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    interchange-add-add-Large-Ab :
      {l1 l2 l3 l4 : Level}
      (a : type-Large-Ab G l1) (b : type-Large-Ab G l2)
      (c : type-Large-Ab G l3) (d : type-Large-Ab G l4) →
      add-Large-Ab G (add-Large-Ab G a b) (add-Large-Ab G c d) ＝
      add-Large-Ab G (add-Large-Ab G a c) (add-Large-Ab G b d)
    interchange-add-add-Large-Ab =
      interchange-mul-mul-Large-Commutative-Monoid
        ( large-commutative-monoid-Large-Ab G)
```
