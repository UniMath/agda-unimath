# Large Heyting fields

```agda
{-# OPTIONS --lossy-unification #-}

module commutative-algebra.large-heyting-fields where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields
open import commutative-algebra.large-commutative-rings
open import commutative-algebra.local-commutative-rings

open import foundation.cumulative-large-sets
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.embeddings
open import foundation.function-types
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.large-binary-relations
open import foundation.large-similarity-relations
open import foundation.logical-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.similarity-preserving-binary-maps-cumulative-large-sets
open import foundation.similarity-preserving-maps-cumulative-large-sets
open import foundation.universe-levels

open import group-theory.invertible-elements-large-monoids
open import group-theory.large-commutative-monoids
open import group-theory.large-monoids

open import ring-theory.large-rings
```

</details>

## Idea

## Definition

```agda
record
  Large-Heyting-Field
  (α : Level → Level) (β : Level → Level → Level) : UUω where

  constructor
    make-Large-Heyting-Field

  field
    large-commutative-ring-Large-Heyting-Field : Large-Commutative-Ring α β

  large-ring-Large-Heyting-Field : Large-Ring α β
  large-ring-Large-Heyting-Field =
    large-ring-Large-Commutative-Ring
      ( large-commutative-ring-Large-Heyting-Field)

  cumulative-large-set-Large-Heyting-Field : Cumulative-Large-Set α β
  cumulative-large-set-Large-Heyting-Field =
    cumulative-large-set-Large-Commutative-Ring
      ( large-commutative-ring-Large-Heyting-Field)

  type-Large-Heyting-Field : (l : Level) → UU (α l)
  type-Large-Heyting-Field =
    type-Large-Commutative-Ring large-commutative-ring-Large-Heyting-Field

  large-commutative-monoid-mul-Large-Heyting-Field :
    Large-Commutative-Monoid α β
  large-commutative-monoid-mul-Large-Heyting-Field =
    large-commutative-monoid-mul-Large-Commutative-Ring
      ( large-commutative-ring-Large-Heyting-Field)

  large-monoid-mul-Large-Heyting-Field : Large-Monoid α β
  large-monoid-mul-Large-Heyting-Field =
    large-monoid-Large-Commutative-Monoid
      large-commutative-monoid-mul-Large-Heyting-Field

  is-invertible-element-prop-Large-Heyting-Field :
    {l : Level} (x : type-Large-Heyting-Field l) → Prop (α l ⊔ β l lzero)
  is-invertible-element-prop-Large-Heyting-Field =
    is-invertible-element-prop-Large-Monoid large-monoid-mul-Large-Heyting-Field

  is-invertible-element-Large-Heyting-Field :
    {l : Level} (x : type-Large-Heyting-Field l) → UU (α l ⊔ β l lzero)
  is-invertible-element-Large-Heyting-Field x =
    type-Prop (is-invertible-element-prop-Large-Heyting-Field x)

  add-Large-Heyting-Field :
    {l1 l2 : Level} →
    type-Large-Heyting-Field l1 → type-Large-Heyting-Field l2 →
    type-Large-Heyting-Field (l1 ⊔ l2)
  add-Large-Heyting-Field =
    add-Large-Commutative-Ring
      ( large-commutative-ring-Large-Heyting-Field)

  zero-Large-Heyting-Field : type-Large-Heyting-Field lzero
  zero-Large-Heyting-Field =
    zero-Large-Commutative-Ring large-commutative-ring-Large-Heyting-Field

  is-zero-prop-Large-Heyting-Field :
    {l : Level} → type-Large-Heyting-Field l → Prop (β l lzero)
  is-zero-prop-Large-Heyting-Field =
    is-zero-prop-Large-Commutative-Ring
      ( large-commutative-ring-Large-Heyting-Field)

  is-zero-Large-Heyting-Field :
    {l : Level} → type-Large-Heyting-Field l → UU (β l lzero)
  is-zero-Large-Heyting-Field x =
    type-Prop (is-zero-prop-Large-Heyting-Field x)

  one-Large-Heyting-Field : type-Large-Heyting-Field lzero
  one-Large-Heyting-Field =
    one-Large-Commutative-Ring large-commutative-ring-Large-Heyting-Field

  field
    is-local-Large-Heyting-Field :
      {l1 l2 : Level}
      (x : type-Large-Heyting-Field l1) (y : type-Large-Heyting-Field l2) →
      is-invertible-element-Large-Heyting-Field (add-Large-Heyting-Field x y) →
      disjunction-type
        ( is-invertible-element-Large-Heyting-Field x)
        ( is-invertible-element-Large-Heyting-Field y)

    is-nontrivial-Large-Heyting-Field :
      zero-Large-Heyting-Field ≠ one-Large-Heyting-Field

    is-zero-is-not-invertible-element-Large-Heyting-Field :
      {l : Level} (x : type-Large-Heyting-Field l) →
      ¬ is-invertible-element-Large-Heyting-Field x →
      is-zero-Large-Heyting-Field x

open Large-Heyting-Field public
```

## Properties

### Operations

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (K : Large-Heyting-Field α β)
  where

  add-Large-Heyting-Field' :
    {l1 l2 : Level} →
    type-Large-Heyting-Field K l1 → type-Large-Heyting-Field K l2 →
    type-Large-Heyting-Field K (l1 ⊔ l2)
  add-Large-Heyting-Field' x y = add-Large-Heyting-Field K y x

  mul-Large-Heyting-Field :
    {l1 l2 : Level} →
    type-Large-Heyting-Field K l1 → type-Large-Heyting-Field K l2 →
    type-Large-Heyting-Field K (l1 ⊔ l2)
  mul-Large-Heyting-Field =
    mul-Large-Commutative-Ring (large-commutative-ring-Large-Heyting-Field K)

  diff-Large-Heyting-Field :
    {l1 l2 : Level} →
    type-Large-Heyting-Field K l1 → type-Large-Heyting-Field K l2 →
    type-Large-Heyting-Field K (l1 ⊔ l2)
  diff-Large-Heyting-Field =
    diff-Large-Commutative-Ring (large-commutative-ring-Large-Heyting-Field K)

  neg-Large-Heyting-Field :
    {l : Level} →
    type-Large-Heyting-Field K l → type-Large-Heyting-Field K l
  neg-Large-Heyting-Field =
    neg-Large-Commutative-Ring (large-commutative-ring-Large-Heyting-Field K)
```

### Similarity

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (K : Large-Heyting-Field α β)
  where

  large-similarity-relation-Large-Heyting-Field :
    Large-Similarity-Relation β (type-Large-Heyting-Field K)
  large-similarity-relation-Large-Heyting-Field =
    large-similarity-relation-Large-Ring (large-ring-Large-Heyting-Field K)

  sim-prop-Large-Heyting-Field :
    Large-Relation-Prop β (type-Large-Heyting-Field K)
  sim-prop-Large-Heyting-Field =
    sim-prop-Large-Ring (large-ring-Large-Heyting-Field K)

  sim-Large-Heyting-Field : Large-Relation β (type-Large-Heyting-Field K)
  sim-Large-Heyting-Field =
    sim-Large-Ring (large-ring-Large-Heyting-Field K)

  refl-sim-Large-Heyting-Field :
    is-reflexive-Large-Relation
      ( type-Large-Heyting-Field K)
      ( sim-Large-Heyting-Field)
  refl-sim-Large-Heyting-Field =
    refl-sim-Large-Ring (large-ring-Large-Heyting-Field K)

  symmetric-sim-Large-Heyting-Field :
    is-symmetric-Large-Relation
      ( type-Large-Heyting-Field K)
      ( sim-Large-Heyting-Field)
  symmetric-sim-Large-Heyting-Field =
    symmetric-sim-Large-Ring (large-ring-Large-Heyting-Field K)

  transitive-sim-Large-Heyting-Field :
    is-transitive-Large-Relation
      ( type-Large-Heyting-Field K)
      ( sim-Large-Heyting-Field)
  transitive-sim-Large-Heyting-Field =
    transitive-sim-Large-Ring (large-ring-Large-Heyting-Field K)

  sim-eq-Large-Heyting-Field :
    {l : Level} {x y : type-Large-Heyting-Field K l} →
    x ＝ y → sim-Large-Heyting-Field x y
  sim-eq-Large-Heyting-Field =
    sim-eq-Large-Ring (large-ring-Large-Heyting-Field K)

  eq-sim-Large-Heyting-Field :
    {l : Level} (x y : type-Large-Heyting-Field K l) →
    sim-Large-Heyting-Field x y → x ＝ y
  eq-sim-Large-Heyting-Field =
    eq-sim-Large-Ring (large-ring-Large-Heyting-Field K)
```

### Similarity reasoning on large rings

```agda
module
  similarity-reasoning-Large-Heyting-Field
    {α : Level → Level} {β : Level → Level → Level} (K : Large-Heyting-Field α β)
  where

  open similarity-reasoning-Large-Ring (large-ring-Large-Heyting-Field K) public
```

### Raising universe levels

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (K : Large-Heyting-Field α β)
  where

  raise-Large-Heyting-Field :
    {l0 : Level} (l : Level) →
    type-Large-Heyting-Field K l0 → type-Large-Heyting-Field K (l0 ⊔ l)
  raise-Large-Heyting-Field =
    raise-Large-Ring (large-ring-Large-Heyting-Field K)

  sim-raise-Large-Heyting-Field :
    {l0 : Level} (l : Level) (x : type-Large-Heyting-Field K l0) →
    sim-Large-Heyting-Field K x (raise-Large-Heyting-Field l x)
  sim-raise-Large-Heyting-Field =
    sim-raise-Large-Ring (large-ring-Large-Heyting-Field K)

  sim-raise-Large-Heyting-Field' :
    {l0 : Level} (l : Level) (x : type-Large-Heyting-Field K l0) →
    sim-Large-Heyting-Field K (raise-Large-Heyting-Field l x) x
  sim-raise-Large-Heyting-Field' =
    sim-raise-Large-Ring' (large-ring-Large-Heyting-Field K)

  eq-raise-Large-Heyting-Field :
    {l : Level} (x : type-Large-Heyting-Field K l) → raise-Large-Heyting-Field l x ＝ x
  eq-raise-Large-Heyting-Field =
    eq-raise-Large-Ring (large-ring-Large-Heyting-Field K)

  is-emb-raise-Large-Heyting-Field :
    (l1 l2 : Level) → is-emb (raise-Large-Heyting-Field {l1} l2)
  is-emb-raise-Large-Heyting-Field =
    is-emb-raise-Large-Ring (large-ring-Large-Heyting-Field K)

  emb-raise-Large-Heyting-Field :
    (l1 l2 : Level) → type-Large-Heyting-Field K l1 ↪ type-Large-Heyting-Field K (l1 ⊔ l2)
  emb-raise-Large-Heyting-Field =
    emb-raise-Large-Ring (large-ring-Large-Heyting-Field K)

  raise-raise-Large-Heyting-Field :
    {l0 l1 l2 : Level} (x : type-Large-Heyting-Field K l0) →
    raise-Large-Heyting-Field l1 (raise-Large-Heyting-Field l2 x) ＝
    raise-Large-Heyting-Field (l1 ⊔ l2) x
  raise-raise-Large-Heyting-Field =
    raise-raise-Large-Ring (large-ring-Large-Heyting-Field K)

  eq-raise-sim-Large-Heyting-Field :
    {l1 l2 : Level}
    (x : type-Large-Heyting-Field K l1) (y : type-Large-Heyting-Field K l2) →
    sim-Large-Heyting-Field K x y →
    raise-Large-Heyting-Field l2 x ＝ raise-Large-Heyting-Field l1 y
  eq-raise-sim-Large-Heyting-Field =
    eq-raise-sim-Large-Ring (large-ring-Large-Heyting-Field K)

  sim-eq-raise-Large-Heyting-Field :
    {l1 l2 : Level}
    (x : type-Large-Heyting-Field K l1) (y : type-Large-Heyting-Field K l2) →
    raise-Large-Heyting-Field l2 x ＝ raise-Large-Heyting-Field l1 y →
    sim-Large-Heyting-Field K x y
  sim-eq-raise-Large-Heyting-Field =
    sim-eq-raise-Large-Ring (large-ring-Large-Heyting-Field K)

  eq-raise-iff-sim-Large-Heyting-Field :
    {l1 l2 : Level} →
    (x : type-Large-Heyting-Field K l1) (y : type-Large-Heyting-Field K l2) →
    ( sim-Large-Heyting-Field K x y ↔
      ( raise-Large-Heyting-Field l2 x ＝ raise-Large-Heyting-Field l1 y))
  eq-raise-iff-sim-Large-Heyting-Field =
    eq-raise-iff-sim-Large-Ring (large-ring-Large-Heyting-Field K)

  eq-raise-sim-Large-Heyting-Field' :
    {l1 l2 : Level}
    (x : type-Large-Heyting-Field K (l1 ⊔ l2))
    (y : type-Large-Heyting-Field K l2) →
    sim-Large-Heyting-Field K x y → x ＝ raise-Large-Heyting-Field l1 y
  eq-raise-sim-Large-Heyting-Field' =
    eq-raise-sim-Large-Ring' (large-ring-Large-Heyting-Field K)
```

### Similarity preservation of addition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (K : Large-Heyting-Field α β)
  where

  sim-preserving-binary-operator-add-Large-Heyting-Field :
    sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Heyting-Field K)
  sim-preserving-binary-operator-add-Large-Heyting-Field =
    sim-preserving-binary-operator-add-Large-Ring
      ( large-ring-Large-Heyting-Field K)

  preserves-sim-add-Large-Heyting-Field :
    preserves-sim-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Heyting-Field K)
      ( add-Large-Heyting-Field K)
  preserves-sim-add-Large-Heyting-Field =
    preserves-sim-add-Large-Ring (large-ring-Large-Heyting-Field K)

  sim-preserving-map-left-add-Large-Heyting-Field :
    {l : Level} (x : type-Large-Heyting-Field K l) →
    sim-preserving-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Heyting-Field K)
  sim-preserving-map-left-add-Large-Heyting-Field =
    sim-preserving-map-left-add-Large-Ring (large-ring-Large-Heyting-Field K)

  preserves-sim-left-add-Large-Heyting-Field :
    {l : Level} (x : type-Large-Heyting-Field K l) →
    preserves-sim-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Heyting-Field K)
      ( add-Large-Heyting-Field K x)
  preserves-sim-left-add-Large-Heyting-Field =
    preserves-sim-left-add-Large-Ring (large-ring-Large-Heyting-Field K)

  sim-preserving-map-right-add-Large-Heyting-Field :
    {l : Level} (y : type-Large-Heyting-Field K l) →
    sim-preserving-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Heyting-Field K)
  sim-preserving-map-right-add-Large-Heyting-Field =
    sim-preserving-map-right-add-Large-Ring
      ( large-ring-Large-Heyting-Field K)

  preserves-sim-right-add-Large-Heyting-Field :
    {l : Level} (y : type-Large-Heyting-Field K l) →
    preserves-sim-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Heyting-Field K)
      ( add-Large-Heyting-Field' K y)
  preserves-sim-right-add-Large-Heyting-Field =
    preserves-sim-right-add-Large-Ring (large-ring-Large-Heyting-Field K)
```

### Raising universe levels in addition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (K : Large-Heyting-Field α β)
  where

  abstract
    add-raise-right-Large-Heyting-Field :
      {l1 l2 : Level} (l3 : Level) →
      (x : type-Large-Heyting-Field K l1) (y : type-Large-Heyting-Field K l2) →
      add-Large-Heyting-Field K x (raise-Large-Heyting-Field K l3 y) ＝
      raise-Large-Heyting-Field K l3 (add-Large-Heyting-Field K x y)
    add-raise-right-Large-Heyting-Field =
      add-raise-right-Large-Ring (large-ring-Large-Heyting-Field K)

    add-raise-left-Large-Heyting-Field :
      {l1 l2 : Level} (l3 : Level) →
      (x : type-Large-Heyting-Field K l1) (y : type-Large-Heyting-Field K l2) →
      add-Large-Heyting-Field K (raise-Large-Heyting-Field K l3 x) y ＝
      raise-Large-Heyting-Field K l3 (add-Large-Heyting-Field K x y)
    add-raise-left-Large-Heyting-Field =
      add-raise-left-Large-Ring (large-ring-Large-Heyting-Field K)

    add-raise-raise-Large-Heyting-Field :
      {l1 l2 : Level} (l3 l4 : Level) →
      (x : type-Large-Heyting-Field K l1) (y : type-Large-Heyting-Field K l2) →
      add-Large-Heyting-Field K
        ( raise-Large-Heyting-Field K l3 x)
        ( raise-Large-Heyting-Field K l4 y) ＝
      raise-Large-Heyting-Field K (l3 ⊔ l4) (add-Large-Heyting-Field K x y)
    add-raise-raise-Large-Heyting-Field =
      add-raise-raise-Large-Ring (large-ring-Large-Heyting-Field K)
```

### The negation operation preserves similarity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (K : Large-Heyting-Field α β)
  where

  sim-preserving-endomap-neg-Large-Heyting-Field :
    sim-preserving-endomap-Cumulative-Large-Set
      ( id)
      ( cumulative-large-set-Large-Heyting-Field K)
  sim-preserving-endomap-neg-Large-Heyting-Field =
    sim-preserving-endomap-neg-Large-Ring (large-ring-Large-Heyting-Field K)

  preserves-sim-neg-Large-Heyting-Field :
    preserves-sim-endomap-Cumulative-Large-Set
      ( id)
      ( cumulative-large-set-Large-Heyting-Field K)
      ( neg-Large-Heyting-Field K)
  preserves-sim-neg-Large-Heyting-Field =
    preserves-sim-neg-Large-Ring (large-ring-Large-Heyting-Field K)
```

### Semigroup laws of addition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (K : Large-Heyting-Field α β)
  where

  associative-add-Large-Heyting-Field :
    {l1 l2 l3 : Level}
    (x : type-Large-Heyting-Field K l1)
    (y : type-Large-Heyting-Field K l2)
    (z : type-Large-Heyting-Field K l3) →
    add-Large-Heyting-Field K (add-Large-Heyting-Field K x y) z ＝
    add-Large-Heyting-Field K x (add-Large-Heyting-Field K y z)
  associative-add-Large-Heyting-Field =
    associative-add-Large-Ring (large-ring-Large-Heyting-Field K)
```

### Monoid laws of addition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (K : Large-Heyting-Field α β)
  where

  raise-zero-Large-Heyting-Field :
    (l : Level) → type-Large-Heyting-Field K l
  raise-zero-Large-Heyting-Field =
    raise-zero-Large-Ring (large-ring-Large-Heyting-Field K)

  is-zero-zero-Large-Heyting-Field :
    is-zero-Large-Heyting-Field K (zero-Large-Heyting-Field K)
  is-zero-zero-Large-Heyting-Field =
    is-zero-zero-Large-Ring (large-ring-Large-Heyting-Field K)

  is-zero-raise-zero-Large-Heyting-Field :
    (l : Level) →
    is-zero-Large-Heyting-Field K (raise-zero-Large-Heyting-Field l)
  is-zero-raise-zero-Large-Heyting-Field =
    is-zero-raise-zero-Large-Ring (large-ring-Large-Heyting-Field K)

  eq-raise-zero-is-zero-Large-Heyting-Field :
    {l : Level} (x : type-Large-Heyting-Field K l) →
    is-zero-Large-Heyting-Field K x → x ＝ raise-zero-Large-Heyting-Field l
  eq-raise-zero-is-zero-Large-Heyting-Field =
    eq-raise-zero-is-zero-Large-Ring (large-ring-Large-Heyting-Field K)

  left-unit-law-add-Large-Heyting-Field :
    {l : Level} (x : type-Large-Heyting-Field K l) →
    add-Large-Heyting-Field K (zero-Large-Heyting-Field K) x ＝ x
  left-unit-law-add-Large-Heyting-Field =
    left-unit-law-add-Large-Ring (large-ring-Large-Heyting-Field K)

  right-unit-law-add-Large-Heyting-Field :
    {l : Level} (x : type-Large-Heyting-Field K l) →
    add-Large-Heyting-Field K x (zero-Large-Heyting-Field K) ＝ x
  right-unit-law-add-Large-Heyting-Field =
    right-unit-law-add-Large-Ring (large-ring-Large-Heyting-Field K)

  left-raise-unit-law-add-Large-Heyting-Field :
    {l1 l2 : Level} (y : type-Large-Heyting-Field K l2) →
    add-Large-Heyting-Field K (raise-zero-Large-Heyting-Field l1) y ＝
    raise-Large-Heyting-Field K l1 y
  left-raise-unit-law-add-Large-Heyting-Field =
    left-raise-unit-law-add-Large-Ring (large-ring-Large-Heyting-Field K)

  right-raise-unit-law-add-Large-Heyting-Field :
    {l1 l2 : Level} (x : type-Large-Heyting-Field K l1) →
    add-Large-Heyting-Field K x (raise-zero-Large-Heyting-Field l2) ＝
    raise-Large-Heyting-Field K l2 x
  right-raise-unit-law-add-Large-Heyting-Field =
    right-raise-unit-law-add-Large-Ring (large-ring-Large-Heyting-Field K)

  eq-left-is-zero-law-add-Large-Heyting-Field :
    {l1 l2 : Level}
    (x : type-Large-Heyting-Field K l1) (y : type-Large-Heyting-Field K l2) →
    is-zero-Large-Heyting-Field K x →
    add-Large-Heyting-Field K x y ＝ raise-Large-Heyting-Field K l1 y
  eq-left-is-zero-law-add-Large-Heyting-Field =
    eq-left-is-zero-law-add-Large-Ring (large-ring-Large-Heyting-Field K)

  eq-right-is-zero-law-add-Large-Heyting-Field :
    {l1 l2 : Level}
    (x : type-Large-Heyting-Field K l1) (y : type-Large-Heyting-Field K l2) →
    is-zero-Large-Heyting-Field K y →
    add-Large-Heyting-Field K x y ＝ raise-Large-Heyting-Field K l2 x
  eq-right-is-zero-law-add-Large-Heyting-Field =
    eq-right-is-zero-law-add-Large-Ring (large-ring-Large-Heyting-Field K)

  sim-left-is-zero-law-add-Large-Heyting-Field :
    {l1 l2 : Level}
    (x : type-Large-Heyting-Field K l1) (y : type-Large-Heyting-Field K l2) →
    is-zero-Large-Heyting-Field K x →
    sim-Large-Heyting-Field K (add-Large-Heyting-Field K x y) y
  sim-left-is-zero-law-add-Large-Heyting-Field =
    sim-left-is-zero-law-add-Large-Ring (large-ring-Large-Heyting-Field K)

  sim-right-is-zero-law-add-Large-Heyting-Field :
    {l1 l2 : Level}
    (x : type-Large-Heyting-Field K l1) (y : type-Large-Heyting-Field K l2) →
    is-zero-Large-Heyting-Field K y →
    sim-Large-Heyting-Field K (add-Large-Heyting-Field K x y) x
  sim-right-is-zero-law-add-Large-Heyting-Field =
    sim-right-is-zero-law-add-Large-Ring (large-ring-Large-Heyting-Field K)
```

### Group laws of addition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (K : Large-Heyting-Field α β)
  where

  abstract
    sim-left-inverse-law-add-Large-Heyting-Field :
      {l : Level} (x : type-Large-Heyting-Field K l) →
      is-zero-Large-Heyting-Field K
        ( add-Large-Heyting-Field K (neg-Large-Heyting-Field K x) x)
    sim-left-inverse-law-add-Large-Heyting-Field =
      sim-left-inverse-law-add-Large-Ring (large-ring-Large-Heyting-Field K)

    sim-right-inverse-law-add-Large-Heyting-Field :
      {l : Level} (x : type-Large-Heyting-Field K l) →
      is-zero-Large-Heyting-Field K
        ( add-Large-Heyting-Field K x (neg-Large-Heyting-Field K x))
    sim-right-inverse-law-add-Large-Heyting-Field =
      sim-right-inverse-law-add-Large-Ring (large-ring-Large-Heyting-Field K)

    eq-left-inverse-law-add-Large-Heyting-Field :
      {l : Level} (x : type-Large-Heyting-Field K l) →
      add-Large-Heyting-Field K (neg-Large-Heyting-Field K x) x ＝
      raise-zero-Large-Heyting-Field K l
    eq-left-inverse-law-add-Large-Heyting-Field =
      eq-left-inverse-law-add-Large-Ring (large-ring-Large-Heyting-Field K)

    eq-right-inverse-law-add-Large-Heyting-Field :
      {l : Level} (x : type-Large-Heyting-Field K l) →
      add-Large-Heyting-Field K x (neg-Large-Heyting-Field K x) ＝
      raise-zero-Large-Heyting-Field K l
    eq-right-inverse-law-add-Large-Heyting-Field =
      eq-right-inverse-law-add-Large-Ring (large-ring-Large-Heyting-Field K)

    unique-left-neg-Large-Heyting-Field :
      {l1 l2 : Level}
      (x : type-Large-Heyting-Field K l1) (y : type-Large-Heyting-Field K l2) →
      is-zero-Large-Heyting-Field K (add-Large-Heyting-Field K x y) →
      sim-Large-Heyting-Field K x (neg-Large-Heyting-Field K y)
    unique-left-neg-Large-Heyting-Field =
      unique-left-neg-Large-Ring (large-ring-Large-Heyting-Field K)

    unique-right-neg-Large-Heyting-Field :
      {l1 l2 : Level}
      (x : type-Large-Heyting-Field K l1) (y : type-Large-Heyting-Field K l2) →
      is-zero-Large-Heyting-Field K (add-Large-Heyting-Field K x y) →
      sim-Large-Heyting-Field K y (neg-Large-Heyting-Field K x)
    unique-right-neg-Large-Heyting-Field =
      unique-right-neg-Large-Ring (large-ring-Large-Heyting-Field K)

    distributive-neg-add-Large-Heyting-Field :
      {l1 l2 : Level}
      (x : type-Large-Heyting-Field K l1) (y : type-Large-Heyting-Field K l2) →
      neg-Large-Heyting-Field K (add-Large-Heyting-Field K x y) ＝
      add-Large-Heyting-Field K
        ( neg-Large-Heyting-Field K x)
        ( neg-Large-Heyting-Field K y)
    distributive-neg-add-Large-Heyting-Field x y =
      distributive-neg-add-Large-Ring (large-ring-Large-Heyting-Field K) x y

    neg-is-zero-Large-Heyting-Field :
      {l : Level} (x : type-Large-Heyting-Field K l) →
      is-zero-Large-Heyting-Field K x →
      is-zero-Large-Heyting-Field K (neg-Large-Heyting-Field K x)
    neg-is-zero-Large-Heyting-Field =
      neg-is-zero-Large-Ring (large-ring-Large-Heyting-Field K)

    neg-zero-Large-Heyting-Field :
      neg-Large-Heyting-Field K (zero-Large-Heyting-Field K) ＝
      zero-Large-Heyting-Field K
    neg-zero-Large-Heyting-Field =
      neg-zero-Large-Ring (large-ring-Large-Heyting-Field K)

    neg-raise-zero-Large-Heyting-Field :
      (l : Level) →
      neg-Large-Heyting-Field K (raise-zero-Large-Heyting-Field K l) ＝
      raise-zero-Large-Heyting-Field K l
    neg-raise-zero-Large-Heyting-Field =
      neg-raise-zero-Large-Ring (large-ring-Large-Heyting-Field K)

    neg-neg-Large-Heyting-Field :
      {l : Level} (x : type-Large-Heyting-Field K l) →
      neg-Large-Heyting-Field K (neg-Large-Heyting-Field K x) ＝ x
    neg-neg-Large-Heyting-Field =
      neg-neg-Large-Ring (large-ring-Large-Heyting-Field K)
```

### Cancellation laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (K : Large-Heyting-Field α β)
  {l1 l2 : Level}
  (x : type-Large-Heyting-Field K l1) (y : type-Large-Heyting-Field K l2)
  where

  abstract
    sim-cancel-left-diff-add-Large-Heyting-Field :
      sim-Large-Heyting-Field K
        ( add-Large-Heyting-Field K
          ( neg-Large-Heyting-Field K x)
          ( add-Large-Heyting-Field K x y))
        ( y)
    sim-cancel-left-diff-add-Large-Heyting-Field =
      sim-cancel-left-diff-add-Large-Ring (large-ring-Large-Heyting-Field K) x y

    sim-cancel-left-add-diff-Large-Heyting-Field :
      sim-Large-Heyting-Field K
        ( add-Large-Heyting-Field K
          ( x)
          ( add-Large-Heyting-Field K (neg-Large-Heyting-Field K x) y))
        ( y)
    sim-cancel-left-add-diff-Large-Heyting-Field =
      sim-cancel-left-add-diff-Large-Ring (large-ring-Large-Heyting-Field K) x y

    sim-cancel-right-diff-add-Large-Heyting-Field :
      sim-Large-Heyting-Field K
        ( add-Large-Heyting-Field K
          ( add-Large-Heyting-Field K y (neg-Large-Heyting-Field K x))
          ( x))
        ( y)
    sim-cancel-right-diff-add-Large-Heyting-Field =
      sim-cancel-right-diff-add-Large-Ring
        ( large-ring-Large-Heyting-Field K)
        ( x)
        ( y)

    sim-cancel-right-add-diff-Large-Heyting-Field :
      sim-Large-Heyting-Field K
        ( add-Large-Heyting-Field K
          ( add-Large-Heyting-Field K y x)
          ( neg-Large-Heyting-Field K x))
        ( y)
    sim-cancel-right-add-diff-Large-Heyting-Field =
      sim-cancel-right-add-diff-Large-Ring
        ( large-ring-Large-Heyting-Field K)
        ( x)
        ( y)

    eq-cancel-left-diff-add-Large-Heyting-Field :
      add-Large-Heyting-Field K
        ( neg-Large-Heyting-Field K x)
        ( add-Large-Heyting-Field K x y) ＝
      raise-Large-Heyting-Field K l1 y
    eq-cancel-left-diff-add-Large-Heyting-Field =
      eq-cancel-left-diff-add-Large-Ring (large-ring-Large-Heyting-Field K) x y

    eq-cancel-left-add-diff-Large-Heyting-Field :
      add-Large-Heyting-Field K
        ( x)
        ( add-Large-Heyting-Field K (neg-Large-Heyting-Field K x) y) ＝
      raise-Large-Heyting-Field K l1 y
    eq-cancel-left-add-diff-Large-Heyting-Field =
      eq-cancel-left-add-diff-Large-Ring (large-ring-Large-Heyting-Field K) x y

    eq-cancel-right-diff-add-Large-Heyting-Field :
      add-Large-Heyting-Field K
        ( add-Large-Heyting-Field K y (neg-Large-Heyting-Field K x))
        ( x) ＝
      raise-Large-Heyting-Field K l1 y
    eq-cancel-right-diff-add-Large-Heyting-Field =
      eq-cancel-right-diff-add-Large-Ring (large-ring-Large-Heyting-Field K) x y

    eq-cancel-right-add-diff-Large-Heyting-Field :
      add-Large-Heyting-Field K
        ( add-Large-Heyting-Field K y x)
        ( neg-Large-Heyting-Field K x) ＝
      raise-Large-Heyting-Field K l1 y
    eq-cancel-right-add-diff-Large-Heyting-Field =
      eq-cancel-right-add-diff-Large-Ring (large-ring-Large-Heyting-Field K) x y
```

### Addition reflects similarity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (K : Large-Heyting-Field α β)
  {l1 l2 l3 : Level}
  (z : type-Large-Heyting-Field K l3)
  (x : type-Large-Heyting-Field K l1)
  (y : type-Large-Heyting-Field K l2)
  where

  abstract
    reflects-sim-right-add-Large-Heyting-Field :
      sim-Large-Heyting-Field K
        ( add-Large-Heyting-Field K x z)
        ( add-Large-Heyting-Field K y z) →
      sim-Large-Heyting-Field K x y
    reflects-sim-right-add-Large-Heyting-Field =
      reflects-sim-right-add-Large-Ring (large-ring-Large-Heyting-Field K) z x y

    reflects-sim-left-add-Large-Heyting-Field :
      sim-Large-Heyting-Field K
        ( add-Large-Heyting-Field K z x)
        ( add-Large-Heyting-Field K z y) →
      sim-Large-Heyting-Field K x y
    reflects-sim-left-add-Large-Heyting-Field =
      reflects-sim-left-add-Large-Ring (large-ring-Large-Heyting-Field K) z x y
```

### Addition on the left or right in a large ring is an embedding

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (K : Large-Heyting-Field α β)
  {l1 : Level} (l2 : Level) (x : type-Large-Heyting-Field K l1)
  where

  abstract
    is-emb-left-add-Large-Heyting-Field :
      is-emb (add-Large-Heyting-Field K {l2 = l2} x)
    is-emb-left-add-Large-Heyting-Field =
      is-emb-left-add-Large-Ring (large-ring-Large-Heyting-Field K) l2 x

    is-emb-right-add-Large-Heyting-Field :
      is-emb (add-Large-Heyting-Field' K {l2 = l2} x)
    is-emb-right-add-Large-Heyting-Field =
      is-emb-right-add-Large-Ring (large-ring-Large-Heyting-Field K) l2 x
```

### Small Heyting fields from large Heyting fields

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (K : Large-Heyting-Field α β)
  where

  local-commutative-ring-Large-Heyting-Field :
    (l : Level) → Local-Commutative-Ring (α l)
  local-commutative-ring-Large-Heyting-Field l =
    ( commutative-ring-Large-Commutative-Ring
        ( large-commutative-ring-Large-Heyting-Field K)
        ( l) ,
      λ x y inv-x+y →
        map-disjunction
          ( is-invertible-small-is-invertible-element-Large-Monoid
            ( large-monoid-mul-Large-Heyting-Field K)
            ( x))
          ( is-invertible-small-is-invertible-element-Large-Monoid
            ( large-monoid-mul-Large-Heyting-Field K)
            ( y))
          ( is-local-Large-Heyting-Field K
            ( x)
            ( y)
            ( is-invertible-is-invertible-small-element-Large-Monoid
              ( large-monoid-mul-Large-Heyting-Field K)
              ( add-Large-Heyting-Field K x y)
              ( inv-x+y))))

  heyting-field-Large-Heyting-Field : (l : Level) → Heyting-Field (α l)
  heyting-field-Large-Heyting-Field l =
    ( local-commutative-ring-Large-Heyting-Field l ,
      map-neg
        ( is-injective-emb (emb-raise-Large-Heyting-Field K lzero l))
        ( is-nontrivial-Large-Heyting-Field K) ,
      λ x ¬inv-x →
        eq-raise-zero-is-zero-Large-Heyting-Field K
          ( x)
          ( is-zero-is-not-invertible-element-Large-Heyting-Field K
            ( x)
            ( map-neg
              ( is-invertible-small-is-invertible-element-Large-Monoid
                ( large-monoid-mul-Large-Heyting-Field K)
                ( x))
              ( ¬inv-x))))
```
