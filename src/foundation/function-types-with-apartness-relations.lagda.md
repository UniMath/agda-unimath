# Apartness relations on function types

```agda
module foundation.function-types-with-apartness-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.binary-relations
open import foundation.dependent-function-types-with-apartness-relations
open import foundation.tight-apartness-relations
open import foundation.universe-levels

open import foundation-core.propositions
```

</details>

## Idea

Given a type `Y` with an [apartness relation](foundation.apartness-relations.md)
and an arbitrary type `X`, then the
[function type](foundation.function-types.md) `X → Y` again has an apartness
relation. Two functions `f` and `g` are **apart** in `X → Y` if there
[exists](foundation.existential-quantification.md) an `x : X` such that `f x` is
apart from `g x` in `Y`. If the apartness relation on `Y` is
[tight](foundation.tight-apartness-relations.md) then so is the apartness
relation on `X → Y`.

## Properties

### Apartness on the type of functions into a type with an apartness relation

```agda
module _
  {l1 l2 l3 : Level} (X : UU l1) (Y : Type-With-Apartness l2 l3)
  where

  rel-apart-function-into-Type-With-Apartness :
    Relation-Prop (l1 ⊔ l3) (X → type-Type-With-Apartness Y)
  rel-apart-function-into-Type-With-Apartness =
    rel-apart-Π-Type-With-Apartness X (λ _ → Y)

  apart-function-into-Type-With-Apartness :
    Relation (l1 ⊔ l3) (X → type-Type-With-Apartness Y)
  apart-function-into-Type-With-Apartness =
    apart-Π-Type-With-Apartness X (λ _ → Y)

  is-prop-apart-function-into-Type-With-Apartness :
    (f g : X → type-Type-With-Apartness Y) →
    is-prop (apart-function-into-Type-With-Apartness f g)
  is-prop-apart-function-into-Type-With-Apartness =
    is-prop-apart-Π-Type-With-Apartness X (λ _ → Y)
```

```agda
module _
  {l1 l2 l3 : Level} (X : UU l1) (Y : Type-With-Apartness l2 l3)
  where

  is-antireflexive-apart-function-into-Type-With-Apartness :
    is-antireflexive (rel-apart-function-into-Type-With-Apartness X Y)
  is-antireflexive-apart-function-into-Type-With-Apartness =
    is-antireflexive-apart-Π-Type-With-Apartness X (λ _ → Y)

  is-symmetric-apart-function-into-Type-With-Apartness :
    is-symmetric (apart-function-into-Type-With-Apartness X Y)
  is-symmetric-apart-function-into-Type-With-Apartness =
    is-symmetric-apart-Π-Type-With-Apartness X (λ _ → Y)

  is-apartness-relation-apart-function-into-Type-With-Apartness :
    is-apartness-relation (rel-apart-function-into-Type-With-Apartness X Y)
  is-apartness-relation-apart-function-into-Type-With-Apartness =
    is-apartness-relation-apart-Π-Type-With-Apartness X (λ _ → Y)

  apartness-relation-function-into-Type-With-Apartness :
    Apartness-Relation (l1 ⊔ l3) (X → type-Type-With-Apartness Y)
  apartness-relation-function-into-Type-With-Apartness =
    apartness-relation-Π-Type-With-Apartness X (λ _ → Y)

  is-cotransitive-apart-function-into-Type-With-Apartness :
    is-cotransitive (rel-apart-function-into-Type-With-Apartness X Y)
  is-cotransitive-apart-function-into-Type-With-Apartness =
    is-cotransitive-apart-Π-Type-With-Apartness X (λ _ → Y)

  function-into-Type-With-Apartness : Type-With-Apartness (l1 ⊔ l2) (l1 ⊔ l3)
  function-into-Type-With-Apartness = Π-Type-With-Apartness X (λ _ → Y)
```

### Tight apartness on the type of functions into a type with tight apartness

```agda
module _
  {l1 l2 l3 : Level} (X : UU l1) (Y : Type-With-Tight-Apartness l2 l3)
  where

  rel-apart-function-into-Type-With-Tight-Apartness :
    Relation-Prop (l1 ⊔ l3) (X → type-Type-With-Tight-Apartness Y)
  rel-apart-function-into-Type-With-Tight-Apartness =
    rel-apart-Π-Type-With-Tight-Apartness X (λ _ → Y)

  apart-function-into-Type-With-Tight-Apartness :
    Relation (l1 ⊔ l3) (X → type-Type-With-Tight-Apartness Y)
  apart-function-into-Type-With-Tight-Apartness =
    apart-Π-Type-With-Tight-Apartness X (λ _ → Y)

  is-prop-apart-function-into-Type-With-Tight-Apartness :
    (f g : X → type-Type-With-Tight-Apartness Y) →
    is-prop (apart-function-into-Type-With-Tight-Apartness f g)
  is-prop-apart-function-into-Type-With-Tight-Apartness =
    is-prop-apart-Π-Type-With-Tight-Apartness X (λ _ → Y)

  is-antireflexive-apart-function-into-Type-With-Tight-Apartness :
    is-antireflexive rel-apart-function-into-Type-With-Tight-Apartness
  is-antireflexive-apart-function-into-Type-With-Tight-Apartness =
    is-antireflexive-apart-Π-Type-With-Tight-Apartness X (λ _ → Y)

  is-symmetric-apart-function-into-Type-With-Tight-Apartness :
    is-symmetric apart-function-into-Type-With-Tight-Apartness
  is-symmetric-apart-function-into-Type-With-Tight-Apartness =
    is-symmetric-apart-Π-Type-With-Tight-Apartness X (λ _ → Y)

  is-cotransitive-apart-function-into-Type-With-Tight-Apartness :
    is-cotransitive rel-apart-function-into-Type-With-Tight-Apartness
  is-cotransitive-apart-function-into-Type-With-Tight-Apartness =
    is-cotransitive-apart-Π-Type-With-Tight-Apartness X (λ _ → Y)

  is-apartness-relation-apart-function-into-Type-With-Tight-Apartness :
    is-apartness-relation rel-apart-function-into-Type-With-Tight-Apartness
  is-apartness-relation-apart-function-into-Type-With-Tight-Apartness =
    is-apartness-relation-apart-Π-Type-With-Tight-Apartness X (λ _ → Y)

  apartness-relation-function-into-Type-With-Tight-Apartness :
    Apartness-Relation (l1 ⊔ l3) (X → type-Type-With-Tight-Apartness Y)
  apartness-relation-function-into-Type-With-Tight-Apartness =
    apartness-relation-Π-Type-With-Tight-Apartness X (λ _ → Y)

  is-tight-apart-function-into-Type-With-Tight-Apartness :
    is-tight rel-apart-function-into-Type-With-Tight-Apartness
  is-tight-apart-function-into-Type-With-Tight-Apartness =
    is-tight-apart-Π-Type-With-Tight-Apartness X (λ _ → Y)

  tight-apartness-relation-function-into-Type-With-Tight-Apartness :
    Tight-Apartness-Relation (l1 ⊔ l3) (X → type-Type-With-Tight-Apartness Y)
  tight-apartness-relation-function-into-Type-With-Tight-Apartness =
    tight-apartness-relation-Π-Type-With-Tight-Apartness X (λ _ → Y)

  function-into-Type-With-Tight-Apartness :
    Type-With-Tight-Apartness (l1 ⊔ l2) (l1 ⊔ l3)
  function-into-Type-With-Tight-Apartness =
    Π-Type-With-Tight-Apartness X (λ _ → Y)
```

## See also

- [Dependent function types with apartness relations](foundation.dependent-function-types-with-apartness-relations.md)
