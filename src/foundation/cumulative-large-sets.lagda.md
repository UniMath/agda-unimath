# Cumulative large sets

```agda
module foundation.cumulative-large-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.large-binary-relations
open import foundation.large-similarity-relations
open import foundation.logical-equivalences
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "cumulative large set" Agda=Cumulative-Large-Set}} is a
universe polymorphic type `X : (l : Level) → UU (α l)` equipped with a
[large similarity relation](foundation.large-similarity-relations.md) and an
inclusion map for all [universe levels](foundation.universe-levels.md) `l1` and
`l2`, `raise : X l1 → X (l1 ⊔ l2)`, such that `x` is similar to `raise x`.

## Definition

```agda
record
  Cumulative-Large-Set
    (α : Level → Level)
    (β : Level → Level → Level) :
    UUω
  where

  field
    type-Cumulative-Large-Set : (l : Level) → UU (α l)
    large-similarity-relation-Cumulative-Large-Set :
      Large-Similarity-Relation β type-Cumulative-Large-Set
    raise-Cumulative-Large-Set :
      {l0 : Level} (l : Level) →
      type-Cumulative-Large-Set l0 → type-Cumulative-Large-Set (l ⊔ l0)

  sim-prop-Cumulative-Large-Set :
    Large-Relation-Prop β type-Cumulative-Large-Set
  sim-prop-Cumulative-Large-Set =
    sim-prop-Large-Similarity-Relation
      ( large-similarity-relation-Cumulative-Large-Set)

  sim-Cumulative-Large-Set : Large-Relation β type-Cumulative-Large-Set
  sim-Cumulative-Large-Set =
    large-relation-Large-Relation-Prop
      ( type-Cumulative-Large-Set)
      ( sim-prop-Cumulative-Large-Set)

  refl-sim-Cumulative-Large-Set :
    is-reflexive-Large-Relation
      ( type-Cumulative-Large-Set)
      ( sim-Cumulative-Large-Set)
  refl-sim-Cumulative-Large-Set =
    refl-sim-Large-Similarity-Relation
      ( large-similarity-relation-Cumulative-Large-Set)

  sim-eq-Cumulative-Large-Set :
    {l : Level} {x y : type-Cumulative-Large-Set l} →
    x ＝ y → sim-Cumulative-Large-Set x y
  sim-eq-Cumulative-Large-Set =
    sim-eq-Large-Similarity-Relation
      ( large-similarity-relation-Cumulative-Large-Set)

  symmetric-sim-Cumulative-Large-Set :
    is-symmetric-Large-Relation
      ( type-Cumulative-Large-Set)
      ( sim-Cumulative-Large-Set)
  symmetric-sim-Cumulative-Large-Set =
    symmetric-sim-Large-Similarity-Relation
      ( large-similarity-relation-Cumulative-Large-Set)

  transitive-sim-Cumulative-Large-Set :
    is-transitive-Large-Relation
      ( type-Cumulative-Large-Set)
      ( sim-Cumulative-Large-Set)
  transitive-sim-Cumulative-Large-Set =
    transitive-sim-Large-Similarity-Relation
      ( large-similarity-relation-Cumulative-Large-Set)

  field
    sim-raise-Cumulative-Large-Set :
      {l0 : Level} (l : Level) (x : type-Cumulative-Large-Set l0) →
      sim-Cumulative-Large-Set x (raise-Cumulative-Large-Set l x)

  sim-raise-Cumulative-Large-Set' :
    {l0 : Level} (l : Level) (x : type-Cumulative-Large-Set l0) →
    sim-Cumulative-Large-Set (raise-Cumulative-Large-Set l x) x
  sim-raise-Cumulative-Large-Set' l x =
    symmetric-sim-Cumulative-Large-Set _ _
      ( sim-raise-Cumulative-Large-Set l x)

  eq-sim-Cumulative-Large-Set :
    {l : Level} (x y : type-Cumulative-Large-Set l) →
    sim-Cumulative-Large-Set x y → x ＝ y
  eq-sim-Cumulative-Large-Set =
    eq-sim-Large-Similarity-Relation
      ( large-similarity-relation-Cumulative-Large-Set)

open Cumulative-Large-Set public
```

## Properties

### Each universe level of a cumulative large set forms a set

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (S : Cumulative-Large-Set α β)
  where

  abstract
    is-set-Cumulative-Large-Set :
      (l : Level) → is-set (type-Cumulative-Large-Set S l)
    is-set-Cumulative-Large-Set =
      is-set-type-Large-Similarity-Relation
        ( large-similarity-relation-Cumulative-Large-Set S)

  set-Cumulative-Large-Set : (l : Level) → Set (α l)
  set-Cumulative-Large-Set l =
    ( type-Cumulative-Large-Set S l , is-set-Cumulative-Large-Set l)
```

### Similarity reasoning

Large cumulative sets can be equationally reasoned in the following way:

```text
let
  open similarity-reasoning-Cumulative-Large-Set S
in
  similarity-reasoning
    x ~ y by sim-1
      ~ z by sim-2
```

```agda
module
  similarity-reasoning-Cumulative-Large-Set
    {α : Level → Level} {β : Level → Level → Level}
    (S : Cumulative-Large-Set α β)
  where

  open
    similarity-reasoning-Large-Similarity-Relation
      ( large-similarity-relation-Cumulative-Large-Set S)
    public
```

### The universe-raising operation in a cumulative large set is an embedding

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (S : Cumulative-Large-Set α β)
  where

  abstract
    is-injective-raise-Cumulative-Large-Set :
      (l1 l2 : Level) →
      is-injective (raise-Cumulative-Large-Set S {l1} l2)
    is-injective-raise-Cumulative-Large-Set l1 l2 {x} {y} rx=ry =
      let
        open similarity-reasoning-Cumulative-Large-Set S
      in
        eq-sim-Cumulative-Large-Set S
          ( x)
          ( y)
          ( similarity-reasoning
            x
            ~ raise-Cumulative-Large-Set S l2 x
              by sim-raise-Cumulative-Large-Set S l2 x
            ~ raise-Cumulative-Large-Set S l2 y
              by sim-eq-Cumulative-Large-Set S rx=ry
            ~ y
              by sim-raise-Cumulative-Large-Set' S l2 y)

    is-emb-raise-Cumulative-Large-Set :
      (l1 l2 : Level) →
      is-emb (raise-Cumulative-Large-Set S {l1} l2)
    is-emb-raise-Cumulative-Large-Set l1 l2 =
      is-emb-is-injective
        ( is-set-Cumulative-Large-Set S (l1 ⊔ l2))
        ( is-injective-raise-Cumulative-Large-Set l1 l2)

  emb-raise-Cumulative-Large-Set :
    (l1 l2 : Level) →
    type-Cumulative-Large-Set S l1 ↪ type-Cumulative-Large-Set S (l1 ⊔ l2)
  emb-raise-Cumulative-Large-Set l1 l2 =
    ( raise-Cumulative-Large-Set S l2 ,
      is-emb-raise-Cumulative-Large-Set l1 l2)
```

### Raising an element of a cumulative large set to its own universe level is the identity

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (S : Cumulative-Large-Set α β)
  where

  abstract
    eq-raise-Cumulative-Large-Set :
      {l : Level} (x : type-Cumulative-Large-Set S l) →
      raise-Cumulative-Large-Set S l x ＝ x
    eq-raise-Cumulative-Large-Set {l} x =
      eq-sim-Cumulative-Large-Set S _ _ (sim-raise-Cumulative-Large-Set' S l x)
```

### Two elements of a cumulative large set are similar if and only if they are equal when raised to each other's universe level

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (S : Cumulative-Large-Set α β)
  where

  abstract
    eq-raise-sim-Cumulative-Large-Set :
      {l1 l2 : Level}
      (x : type-Cumulative-Large-Set S l1)
      (y : type-Cumulative-Large-Set S l2) →
      sim-Cumulative-Large-Set S x y →
      raise-Cumulative-Large-Set S l2 x ＝ raise-Cumulative-Large-Set S l1 y
    eq-raise-sim-Cumulative-Large-Set {l1} {l2} x y x~y =
      let
        open similarity-reasoning-Cumulative-Large-Set S
      in
        eq-sim-Cumulative-Large-Set S _ _
          ( similarity-reasoning
              raise-Cumulative-Large-Set S l2 x
              ~ x
                by sim-raise-Cumulative-Large-Set' S l2 x
              ~ y
                by x~y
              ~ raise-Cumulative-Large-Set S l1 y
                by sim-raise-Cumulative-Large-Set S l1 y)

    sim-eq-raise-Cumulative-Large-Set :
      {l1 l2 : Level}
      {x : type-Cumulative-Large-Set S l1}
      {y : type-Cumulative-Large-Set S l2} →
      raise-Cumulative-Large-Set S l2 x ＝ raise-Cumulative-Large-Set S l1 y →
      sim-Cumulative-Large-Set S x y
    sim-eq-raise-Cumulative-Large-Set {l1} {l2} {x} {y} rx=ry =
      let
        open similarity-reasoning-Cumulative-Large-Set S
      in
        similarity-reasoning
          x
          ~ raise-Cumulative-Large-Set S l2 x
            by sim-raise-Cumulative-Large-Set S l2 x
          ~ raise-Cumulative-Large-Set S l1 y
            by sim-eq-Cumulative-Large-Set S rx=ry
          ~ y
            by sim-raise-Cumulative-Large-Set' S l1 y

  eq-raise-iff-sim-Cumulative-Large-Set :
    {l1 l2 : Level}
    (x : type-Cumulative-Large-Set S l1)
    (y : type-Cumulative-Large-Set S l2) →
    ( sim-Cumulative-Large-Set S x y ↔
      ( raise-Cumulative-Large-Set S l2 x ＝
        raise-Cumulative-Large-Set S l1 y))
  eq-raise-iff-sim-Cumulative-Large-Set x y =
    ( eq-raise-sim-Cumulative-Large-Set x y ,
      sim-eq-raise-Cumulative-Large-Set)
```

### A value raised to one universe level is similar to itself raised to another universe level

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (S : Cumulative-Large-Set α β)
  where

  abstract
    sim-raise-raise-Cumulative-Large-Set :
      {l0 : Level} (l1 l2 : Level) (x : type-Cumulative-Large-Set S l0) →
      sim-Cumulative-Large-Set S
        ( raise-Cumulative-Large-Set S l1 x)
        ( raise-Cumulative-Large-Set S l2 x)
    sim-raise-raise-Cumulative-Large-Set l1 l2 x =
      transitive-sim-Cumulative-Large-Set S _ _ _
        ( sim-raise-Cumulative-Large-Set S l2 x)
        ( sim-raise-Cumulative-Large-Set' S l1 x)
```

### Raising by two universe levels is equivalent to raising by their least upper bound

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (S : Cumulative-Large-Set α β)
  where

  abstract
    raise-raise-Cumulative-Large-Set :
      {l0 : Level} (l1 l2 : Level) (x : type-Cumulative-Large-Set S l0) →
      raise-Cumulative-Large-Set S l1 (raise-Cumulative-Large-Set S l2 x) ＝
      raise-Cumulative-Large-Set S (l1 ⊔ l2) x
    raise-raise-Cumulative-Large-Set l1 l2 x =
      let
        open similarity-reasoning-Cumulative-Large-Set S
      in
        eq-sim-Cumulative-Large-Set S _ _
          ( similarity-reasoning
            raise-Cumulative-Large-Set S l1 (raise-Cumulative-Large-Set S l2 x)
            ~ raise-Cumulative-Large-Set S l2 x
              by sim-raise-Cumulative-Large-Set' S l1 _
            ~ raise-Cumulative-Large-Set S (l1 ⊔ l2) x
              by sim-raise-raise-Cumulative-Large-Set S l2 (l1 ⊔ l2) x)
```
