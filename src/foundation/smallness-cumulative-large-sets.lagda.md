# Smallness in cumulative large sets

```agda
module foundation.smallness-cumulative-large-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cumulative-large-sets
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.smallness-large-similarity-relations
open import foundation.universe-levels
```

</details>

## Idea

Given a [cumulative large set](foundation.cumulative-large-sets.md) `X`, `R` on
a universe-polymorphic type family `X`, an value `x : X l0` is
{{#concept "small" Disambiguation="in a cumulative large set" Agda=is-small-Cumulative-Large-Set}}
relative to a universe level `l` if it is
[small](foundation.smallness-large-similarity-relations.md) relative to `l` in
the [large similarity relation](foundation.large-similarity-relations.md) of
`X`.

## Definition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (X : Cumulative-Large-Set α β)
  where

  is-small-prop-Cumulative-Large-Set :
    {l0 : Level} (l : Level) (x : type-Cumulative-Large-Set X l0) →
    Prop (α l ⊔ β l0 l)
  is-small-prop-Cumulative-Large-Set =
    is-small-prop-Large-Similarity-Relation
      ( large-similarity-relation-Cumulative-Large-Set X)

  is-small-Cumulative-Large-Set :
    {l0 : Level} (l : Level) (x : type-Cumulative-Large-Set X l0) →
    UU (α l ⊔ β l0 l)
  is-small-Cumulative-Large-Set l x =
    type-Prop (is-small-prop-Cumulative-Large-Set l x)

  is-prop-is-small-Cumulative-Large-Set :
    {l0 : Level} (l : Level) (x : type-Cumulative-Large-Set X l0) →
    is-prop (is-small-Cumulative-Large-Set l x)
  is-prop-is-small-Cumulative-Large-Set =
    is-prop-is-small-Large-Similarity-Relation
      ( large-similarity-relation-Cumulative-Large-Set X)
```

## Properties

### An element is small relative to its own universe level

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (X : Cumulative-Large-Set α β)
  where

  is-small-level-Cumulative-Large-Set :
    {l : Level} (x : type-Cumulative-Large-Set X l) →
    is-small-Cumulative-Large-Set X l x
  is-small-level-Cumulative-Large-Set x =
    ( x , refl-sim-Cumulative-Large-Set X x)
```

### An element is small relative to any greater universe level

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (X : Cumulative-Large-Set α β)
  where

  is-small-lub-level-Cumulative-Large-Set :
    {l0 : Level} (l : Level) (x : type-Cumulative-Large-Set X l0) →
    is-small-Cumulative-Large-Set X (l0 ⊔ l) x
  is-small-lub-level-Cumulative-Large-Set l x =
    ( raise-Cumulative-Large-Set X l x ,
      sim-raise-Cumulative-Large-Set X l x)
```
