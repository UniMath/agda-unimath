# Cumulative large sets

```agda
module foundation.cumulative-large-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.large-binary-relations
open import foundation.large-equivalence-relations
open import foundation.large-similarity-relations
open import foundation.logical-equivalences
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

Many structures in mathematics are universe polymorphic in nature, which calls
for some way to compare elements at different universe levels.
[Identity types](foundation-core.identity-types.md) fall short with this respect
because elements at different universe levels don't inhabit the same type. To
solve this issue we have two standard mechanisms: raising universe levels of
elements, and
[large similarity relations](foundation.large-similarity-relations.md).

A {{#concept "cumulative large set" Agda=Cumulative-Large-Set}} captures such a
structure. It is a universe polymorphic type `X : (l : Level) → UU (α l)`
equipped with a
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
      (x : type-Cumulative-Large-Set S l1)
      (y : type-Cumulative-Large-Set S l2) →
      raise-Cumulative-Large-Set S l2 x ＝ raise-Cumulative-Large-Set S l1 y →
      sim-Cumulative-Large-Set S x y
    sim-eq-raise-Cumulative-Large-Set {l1} {l2} x y rx=ry =
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
      sim-eq-raise-Cumulative-Large-Set x y)

  abstract
    eq-raise-sim-Cumulative-Large-Set' :
      {l1 l2 : Level}
      (x : type-Cumulative-Large-Set S (l1 ⊔ l2))
      (y : type-Cumulative-Large-Set S l2) →
      sim-Cumulative-Large-Set S x y → x ＝ raise-Cumulative-Large-Set S l1 y
    eq-raise-sim-Cumulative-Large-Set' {l1} x y x~y =
      eq-sim-Cumulative-Large-Set S
        ( x)
        ( raise-Cumulative-Large-Set S l1 y)
        ( transitive-sim-Cumulative-Large-Set S
          ( x)
          ( y)
          ( raise-Cumulative-Large-Set S l1 y)
          ( sim-raise-Cumulative-Large-Set S l1 y)
          ( x~y))
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
      {l0 l1 l2 : Level} (x : type-Cumulative-Large-Set S l0) →
      raise-Cumulative-Large-Set S l1 (raise-Cumulative-Large-Set S l2 x) ＝
      raise-Cumulative-Large-Set S (l1 ⊔ l2) x
    raise-raise-Cumulative-Large-Set {l0} {l1} {l2} x =
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

### Raising an element of a cumulative large set to its own universe level, or any lesser level, is the identity

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

    eq-raise-leq-level-Cumulative-Large-Set :
      (l1 : Level) {l2 : Level} (x : type-Cumulative-Large-Set S (l1 ⊔ l2)) →
      raise-Cumulative-Large-Set S l2 x ＝ x
    eq-raise-leq-level-Cumulative-Large-Set l1 {l2} x =
      equational-reasoning
        raise-Cumulative-Large-Set S l2 x
        ＝
          raise-Cumulative-Large-Set S
            ( l2)
            ( raise-Cumulative-Large-Set S (l1 ⊔ l2) x)
          by
            ap
              ( raise-Cumulative-Large-Set S l2)
              ( inv (eq-raise-Cumulative-Large-Set x))
        ＝ raise-Cumulative-Large-Set S (l1 ⊔ l2) x
          by raise-raise-Cumulative-Large-Set S x
        ＝ x
          by eq-raise-Cumulative-Large-Set x
```

### A universe-raising operation on a universe-polymorphic family of sets induces a cumulative large set

```agda
module _
  {α : Level → Level}
  (X : (l : Level) → Set (α l))
  (raise-X : {l0 : Level} (l : Level) → type-Set (X l0) ↪ type-Set (X (l ⊔ l0)))
  (raise-raise-X :
    {l0 : Level} (l1 l2 : Level) (x : type-Set (X l0)) →
    map-emb (raise-X l1) (map-emb (raise-X l2) x) ＝
    map-emb (raise-X (l1 ⊔ l2)) x)
  where

  sim-prop-induced-raise :
    Large-Relation-Prop (λ l1 l2 → α (l1 ⊔ l2)) (λ l → type-Set (X l))
  sim-prop-induced-raise {l1} {l2} x y =
    Id-Prop (X (l1 ⊔ l2)) (map-emb (raise-X l2) x) (map-emb (raise-X l1) y)

  sim-induced-raise :
    Large-Relation (λ l1 l2 → α (l1 ⊔ l2)) (λ l → type-Set (X l))
  sim-induced-raise =
    large-relation-Large-Relation-Prop
      ( λ l → type-Set (X l))
      ( sim-prop-induced-raise)

  refl-sim-induced-raise :
    is-reflexive-Large-Relation (λ l → type-Set (X l)) sim-induced-raise
  refl-sim-induced-raise x = refl

  symmetric-sim-induced-raise :
    is-symmetric-Large-Relation (λ l → type-Set (X l)) sim-induced-raise
  symmetric-sim-induced-raise _ _ = inv

  commute-induced-raise :
    {l0 : Level} (l1 l2 : Level) (x : type-Set (X l0)) →
    map-emb (raise-X l1) (map-emb (raise-X l2) x) ＝
    map-emb (raise-X l2) (map-emb (raise-X l1) x)
  commute-induced-raise l1 l2 x =
    raise-raise-X l1 l2 x ∙ inv (raise-raise-X l2 l1 x)

  transitive-sim-induced-raise :
    is-transitive-Large-Relation (λ l → type-Set (X l)) sim-induced-raise
  transitive-sim-induced-raise {l1} {l2} {l3} x y z r3y=r2z r2x=r1y =
    is-injective-emb
      ( raise-X l2)
      ( equational-reasoning
        map-emb (raise-X l2) (map-emb (raise-X l3) x)
        ＝ map-emb (raise-X l3) (map-emb (raise-X l2) x)
          by commute-induced-raise l2 l3 x
        ＝ map-emb (raise-X l3) (map-emb (raise-X l1) y)
          by ap (map-emb (raise-X l3)) r2x=r1y
        ＝ map-emb (raise-X l1) (map-emb (raise-X l3) y)
          by commute-induced-raise l3 l1 y
        ＝ map-emb (raise-X l1) (map-emb (raise-X l2) z)
          by ap (map-emb (raise-X l1)) r3y=r2z
        ＝ map-emb (raise-X l2) (map-emb (raise-X l1) z)
          by commute-induced-raise l1 l2 z)

  eq-sim-induced-raise :
    {l : Level} (x y : type-Set (X l)) → sim-induced-raise x y → x ＝ y
  eq-sim-induced-raise {l} x y = is-injective-emb (raise-X l)

  large-equivalence-relation-induced-raise :
    Large-Equivalence-Relation (λ l1 l2 → α (l1 ⊔ l2)) (λ l → type-Set (X l))
  large-equivalence-relation-induced-raise =
    λ where
      .sim-prop-Large-Equivalence-Relation → sim-prop-induced-raise
      .refl-sim-Large-Equivalence-Relation → refl-sim-induced-raise
      .symmetric-sim-Large-Equivalence-Relation → symmetric-sim-induced-raise
      .transitive-sim-Large-Equivalence-Relation → transitive-sim-induced-raise

  large-similarity-relation-induced-raise :
    Large-Similarity-Relation (λ l1 l2 → α (l1 ⊔ l2)) (λ l → type-Set (X l))
  large-similarity-relation-induced-raise =
    λ where
      .large-equivalence-relation-Large-Similarity-Relation →
        large-equivalence-relation-induced-raise
      .eq-sim-Large-Similarity-Relation → eq-sim-induced-raise

  sim-raise-induced-raise :
    {l0 : Level} (l : Level) (x : type-Set (X l0)) →
    sim-induced-raise x (map-emb (raise-X l) x)
  sim-raise-induced-raise {l0} l x = inv (raise-raise-X l0 l x)

  cumulative-large-set-induced-raise :
    Cumulative-Large-Set α (λ l1 l2 → α (l1 ⊔ l2))
  cumulative-large-set-induced-raise =
    λ where
      .type-Cumulative-Large-Set l → type-Set (X l)
      .large-similarity-relation-Cumulative-Large-Set →
        large-similarity-relation-induced-raise
      .raise-Cumulative-Large-Set l → map-emb (raise-X l)
      .sim-raise-Cumulative-Large-Set → sim-raise-induced-raise
```

## See also

- [Global subuniverses](foundation.global-subuniverses.md)
