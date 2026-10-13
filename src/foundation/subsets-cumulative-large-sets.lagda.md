# Subsets of cumulative large sets

```agda
module foundation.subsets-cumulative-large-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cumulative-large-sets
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.induced-large-similarity-relations-large-subtypes
open import foundation.large-similarity-relations
open import foundation.large-subtypes
open import foundation.propositions
open import foundation.similarity-preserving-maps-cumulative-large-sets
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "subset" Disambiguation="of a cumulative large set" Agda=Subset-Cumulative-Large-Set}}
of a [cumulative large set](foundation.cumulative-large-sets.md) `X` is a
[large subtype](foundation.large-subtypes.md) `S` of `X` such that if `x` is
similar to `y` and `x ∈ S`, then `y ∈ S`.

## Definition

```agda
record
  Subset-Cumulative-Large-Set
    { α : Level → Level}
    { β : Level → Level → Level}
    ( γ : Level → Level)
    ( S : Cumulative-Large-Set α β) :
    UUω
  where

  constructor
    make-Subset-Cumulative-Large-Set

  field
    large-subtype-Subset-Cumulative-Large-Set :
      large-subtype γ (type-Cumulative-Large-Set S)

  type-Subset-Cumulative-Large-Set :
    (l : Level) → UU (α l ⊔ γ l)
  type-Subset-Cumulative-Large-Set =
    type-large-subtype large-subtype-Subset-Cumulative-Large-Set

  is-in-Subset-Cumulative-Large-Set :
    {l : Level} → type-Cumulative-Large-Set S l → UU (γ l)
  is-in-Subset-Cumulative-Large-Set =
    is-in-large-subtype large-subtype-Subset-Cumulative-Large-Set

  prop-is-in-Subset-Cumulative-Large-Set :
    {l : Level} → type-Cumulative-Large-Set S l → Prop (γ l)
  prop-is-in-Subset-Cumulative-Large-Set =
    prop-is-in-large-subtype large-subtype-Subset-Cumulative-Large-Set

  inclusion-Subset-Cumulative-Large-Set :
    {l : Level} →
    type-Subset-Cumulative-Large-Set l → type-Cumulative-Large-Set S l
  inclusion-Subset-Cumulative-Large-Set =
    inclusion-large-subtype large-subtype-Subset-Cumulative-Large-Set

  field
    sim-is-in-Subset-Cumulative-Large-Set :
      {l1 l2 : Level}
      (x : type-Cumulative-Large-Set S l1)
      (y : type-Cumulative-Large-Set S l2) →
      sim-Cumulative-Large-Set S x y →
      is-in-Subset-Cumulative-Large-Set x →
      is-in-Subset-Cumulative-Large-Set y

  sim-is-in-Subset-Cumulative-Large-Set' :
    {l1 l2 : Level}
    (x : type-Cumulative-Large-Set S l1)
    (y : type-Cumulative-Large-Set S l2) →
    sim-Cumulative-Large-Set S x y →
    is-in-Subset-Cumulative-Large-Set y →
    is-in-Subset-Cumulative-Large-Set x
  sim-is-in-Subset-Cumulative-Large-Set' x y x~y y∈S =
    sim-is-in-Subset-Cumulative-Large-Set
      ( y)
      ( x)
      ( symmetric-sim-Cumulative-Large-Set S x y x~y)
      ( y∈S)

open Subset-Cumulative-Large-Set public
```

## Properties

### Identity of elements in a subset of a cumulative large set

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {γ : Level → Level}
  {X : Cumulative-Large-Set α β}
  (S : Subset-Cumulative-Large-Set γ X)
  where

  abstract
    eq-type-Subset-Cumulative-Large-Set :
      {l : Level} {x y : type-Subset-Cumulative-Large-Set S l} →
      ( inclusion-Subset-Cumulative-Large-Set S x ＝
        inclusion-Subset-Cumulative-Large-Set S y) →
      x ＝ y
    eq-type-Subset-Cumulative-Large-Set =
      eq-type-large-subtype (large-subtype-Subset-Cumulative-Large-Set S)
```

### `x` is in a subset if and only if `raise l x` is

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {γ : Level → Level}
  {X : Cumulative-Large-Set α β}
  (S : Subset-Cumulative-Large-Set γ X)
  where

  abstract
    is-closed-under-raise-Subset-Cumulative-Large-Set :
      {l1 : Level} (l2 : Level) (x : type-Cumulative-Large-Set X l1) →
      is-in-Subset-Cumulative-Large-Set S x →
      is-in-Subset-Cumulative-Large-Set S (raise-Cumulative-Large-Set X l2 x)
    is-closed-under-raise-Subset-Cumulative-Large-Set l2 x =
      sim-is-in-Subset-Cumulative-Large-Set
        ( S)
        ( x)
        ( raise-Cumulative-Large-Set X l2 x)
        ( sim-raise-Cumulative-Large-Set X l2 x)

    is-closed-under-raise-Subset-Cumulative-Large-Set' :
      {l1 : Level} (l2 : Level) (x : type-Cumulative-Large-Set X l1) →
      is-in-Subset-Cumulative-Large-Set S (raise-Cumulative-Large-Set X l2 x) →
      is-in-Subset-Cumulative-Large-Set S x
    is-closed-under-raise-Subset-Cumulative-Large-Set' l2 x =
      sim-is-in-Subset-Cumulative-Large-Set'
        ( S)
        ( x)
        ( raise-Cumulative-Large-Set X l2 x)
        ( sim-raise-Cumulative-Large-Set X l2 x)

  raise-type-Subset-Cumulative-Large-Set :
    {l1 : Level} (l2 : Level) →
    type-Subset-Cumulative-Large-Set S l1 →
    type-Subset-Cumulative-Large-Set S (l1 ⊔ l2)
  raise-type-Subset-Cumulative-Large-Set l2 (x , x∈S) =
    ( raise-Cumulative-Large-Set X l2 x ,
      is-closed-under-raise-Subset-Cumulative-Large-Set l2 x x∈S)
```

### A subset induces a cumulative large set

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {γ : Level → Level}
  {X : Cumulative-Large-Set α β}
  (S : Subset-Cumulative-Large-Set γ X)
  where

  large-similarity-relation-Subset-Cumulative-Large-Set :
    Large-Similarity-Relation
      ( β)
      ( type-Subset-Cumulative-Large-Set S)
  large-similarity-relation-Subset-Cumulative-Large-Set =
    large-similarity-relation-large-subtype-Large-Similarity-Relation
      ( large-subtype-Subset-Cumulative-Large-Set S)
      ( large-similarity-relation-Cumulative-Large-Set X)

  cumulative-large-set-Subset-Cumulative-Large-Set :
    Cumulative-Large-Set (λ l → α l ⊔ γ l) β
  cumulative-large-set-Subset-Cumulative-Large-Set =
    make-Cumulative-Large-Set
      ( type-Subset-Cumulative-Large-Set S)
      ( large-similarity-relation-Subset-Cumulative-Large-Set)
      ( raise-type-Subset-Cumulative-Large-Set S)
      ( λ l (x , _) → sim-raise-Cumulative-Large-Set X l x)
```

### The inclusion map on a cumulative large set preserves similarity

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {γ : Level → Level}
  {X : Cumulative-Large-Set α β}
  (S : Subset-Cumulative-Large-Set γ X)
  where

  preserves-sim-inclusion-Subset-Cumulative-Large-Set :
    preserves-sim-map-Cumulative-Large-Set
      ( id)
      ( cumulative-large-set-Subset-Cumulative-Large-Set S)
      ( X)
      ( inclusion-Subset-Cumulative-Large-Set S)
  preserves-sim-inclusion-Subset-Cumulative-Large-Set _ _ x~y = x~y

  sim-preserving-map-inclusion-Subset-Cumulative-Large-Set :
    sim-preserving-map-Cumulative-Large-Set
      ( id)
      ( cumulative-large-set-Subset-Cumulative-Large-Set S)
      ( X)
  sim-preserving-map-inclusion-Subset-Cumulative-Large-Set =
    make-sim-preserving-map-Cumulative-Large-Set
      ( id)
      ( cumulative-large-set-Subset-Cumulative-Large-Set S)
      ( X)
      ( inclusion-Subset-Cumulative-Large-Set S)
      ( preserves-sim-inclusion-Subset-Cumulative-Large-Set)
```
