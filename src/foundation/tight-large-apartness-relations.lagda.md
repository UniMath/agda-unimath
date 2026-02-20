# Tight large apartness relations

```agda
module foundation.tight-large-apartness-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.disjunction
open import foundation.empty-types
open import foundation.identity-types
open import foundation.large-apartness-relations
open import foundation.large-binary-relations
open import foundation.large-equivalence-relations
open import foundation.large-similarity-relations
open import foundation.negation
open import foundation.tight-apartness-relations
open import foundation.universe-levels
```

</details>

## Idea

A [large apartness relation](foundation.large-apartness-relations.md) is
{{#concept "tight" Disambiguation="large apartness relation" Agda=is-tight-Large-Apartness-Relation}}
if it is [tight](foundation.tight-apartness-relations.md) at every universe
level, that is, if `x` and `y` are at the same universe level and are
[not](foundation.negation.md) apart, then they are
[equal](foundation.identity-types.md).

## Definition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {A : (l : Level) → UU (α l)}
  (R : Large-Apartness-Relation β A)
  where

  is-tight-Large-Apartness-Relation : UUω
  is-tight-Large-Apartness-Relation =
    (l : Level) →
    is-tight-Apartness-Relation
      ( apartness-relation-Large-Apartness-Relation R l)

record
  Tight-Large-Apartness-Relation
    {α : Level → Level}
    (β : Level → Level → Level)
    (A : (l : Level) → UU (α l)) : UUω
  where

  field
    large-apartness-relation-Tight-Large-Apartness-Relation :
      Large-Apartness-Relation β A
    is-tight-large-apartness-relation-Tight-Large-Apartness-Relation :
      is-tight-Large-Apartness-Relation
        ( large-apartness-relation-Tight-Large-Apartness-Relation)

  apart-prop-Tight-Large-Apartness-Relation : Large-Relation-Prop β A
  apart-prop-Tight-Large-Apartness-Relation =
    apart-prop-Large-Apartness-Relation
      ( large-apartness-relation-Tight-Large-Apartness-Relation)

  apart-Tight-Large-Apartness-Relation : Large-Relation β A
  apart-Tight-Large-Apartness-Relation =
    apart-Large-Apartness-Relation
      ( large-apartness-relation-Tight-Large-Apartness-Relation)

  antirefl-Tight-Large-Apartness-Relation :
    is-antireflexive-Large-Relation-Prop
      ( A)
      ( apart-prop-Tight-Large-Apartness-Relation)
  antirefl-Tight-Large-Apartness-Relation =
    antirefl-Large-Apartness-Relation
      ( large-apartness-relation-Tight-Large-Apartness-Relation)

  symmetric-Tight-Large-Apartness-Relation :
    is-symmetric-Large-Relation-Prop
      ( A)
      ( apart-prop-Tight-Large-Apartness-Relation)
  symmetric-Tight-Large-Apartness-Relation =
    symmetric-Large-Apartness-Relation
      ( large-apartness-relation-Tight-Large-Apartness-Relation)

  cotransitive-Tight-Large-Apartness-Relation :
    is-cotransitive-Large-Relation-Prop
      ( A)
      ( apart-prop-Tight-Large-Apartness-Relation)
  cotransitive-Tight-Large-Apartness-Relation =
    cotransitive-Large-Apartness-Relation
      ( large-apartness-relation-Tight-Large-Apartness-Relation)

open Tight-Large-Apartness-Relation public
```

## Properties

### A Tight large apartness relation induces a large similarity relation

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {A : (l : Level) → UU (α l)}
  (R : Tight-Large-Apartness-Relation β A)
  where

  sim-prop-Tight-Large-Apartness-Relation : Large-Relation-Prop β A
  sim-prop-Tight-Large-Apartness-Relation x y =
    ¬' apart-prop-Tight-Large-Apartness-Relation R x y

  sim-Tight-Large-Apartness-Relation : Large-Relation β A
  sim-Tight-Large-Apartness-Relation =
    large-relation-Large-Relation-Prop A sim-prop-Tight-Large-Apartness-Relation

  abstract
    refl-sim-Tight-Large-Apartness-Relation :
      is-reflexive-Large-Relation A sim-Tight-Large-Apartness-Relation
    refl-sim-Tight-Large-Apartness-Relation =
      antirefl-Tight-Large-Apartness-Relation R

    symmetric-sim-Tight-Large-Apartness-Relation :
      is-symmetric-Large-Relation A sim-Tight-Large-Apartness-Relation
    symmetric-sim-Tight-Large-Apartness-Relation x y =
      map-neg (symmetric-Tight-Large-Apartness-Relation R y x)

    transitive-sim-Tight-Large-Apartness-Relation :
      is-transitive-Large-Relation A sim-Tight-Large-Apartness-Relation
    transitive-sim-Tight-Large-Apartness-Relation x y z ¬y#z ¬x#y x#z =
      elim-disjunction
        ( empty-Prop)
        ( ¬x#y)
        ( ¬y#z)
        ( cotransitive-Tight-Large-Apartness-Relation R x y z x#z)

    eq-sim-Tight-Large-Apartness-Relation :
      {l : Level} (x y : A l) →
      sim-Tight-Large-Apartness-Relation x y → x ＝ y
    eq-sim-Tight-Large-Apartness-Relation {l} =
      is-tight-large-apartness-relation-Tight-Large-Apartness-Relation R l

  large-equivalence-relation-Tight-Large-Apartness-Relation :
    Large-Equivalence-Relation β A
  large-equivalence-relation-Tight-Large-Apartness-Relation =
    λ where
      .sim-prop-Large-Equivalence-Relation →
        sim-prop-Tight-Large-Apartness-Relation
      .refl-sim-Large-Equivalence-Relation →
        refl-sim-Tight-Large-Apartness-Relation
      .symmetric-sim-Large-Equivalence-Relation →
        symmetric-sim-Tight-Large-Apartness-Relation
      .transitive-sim-Large-Equivalence-Relation →
        transitive-sim-Tight-Large-Apartness-Relation

  large-similarity-relation-Tight-Large-Apartness-Relation :
    Large-Similarity-Relation β A
  large-similarity-relation-Tight-Large-Apartness-Relation =
    λ where
      .large-equivalence-relation-Large-Similarity-Relation →
        large-equivalence-relation-Tight-Large-Apartness-Relation
      .eq-sim-Large-Similarity-Relation →
        eq-sim-Tight-Large-Apartness-Relation
```
