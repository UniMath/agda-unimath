# Large equivalence relations

```agda
module foundation.large-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "large equivalence relation" Agda=Large-Equivalence-Relation}} is a
[large preorder](order-theory.large-preorders.md) that is
[symmetric](foundation.large-binary-relations.md).

## Definition

```agda
record
  Large-Equivalence-Relation
    {α : Level → Level} (β : Level → Level → Level)
    (X : (l : Level) → UU (α l)) : UUω
  where

  constructor
    make-Large-Equivalence-Relation

  field
    sim-prop-Large-Equivalence-Relation : Large-Relation-Prop β X
    refl-sim-Large-Equivalence-Relation :
      is-reflexive-Large-Relation-Prop X sim-prop-Large-Equivalence-Relation
    symmetric-sim-Large-Equivalence-Relation :
      is-symmetric-Large-Relation-Prop X sim-prop-Large-Equivalence-Relation
    transitive-sim-Large-Equivalence-Relation :
      is-transitive-Large-Relation-Prop X sim-prop-Large-Equivalence-Relation

  sim-Large-Equivalence-Relation :
    Large-Relation β X
  sim-Large-Equivalence-Relation x y =
    type-Prop (sim-prop-Large-Equivalence-Relation x y)

  sim-eq-Large-Equivalence-Relation :
    {l : Level} {x y : X l} →
    x ＝ y → sim-Large-Equivalence-Relation x y
  sim-eq-Large-Equivalence-Relation {x = x} x=y =
    tr
      ( sim-Large-Equivalence-Relation x)
      ( x=y)
      ( refl-sim-Large-Equivalence-Relation x)

  equivalence-relation-Large-Equivalence-Relation :
    (l : Level) →
    equivalence-relation (β l l) (X l)
  equivalence-relation-Large-Equivalence-Relation l =
    ( sim-prop-Large-Equivalence-Relation ,
      refl-sim-Large-Equivalence-Relation ,
      symmetric-sim-Large-Equivalence-Relation ,
      transitive-sim-Large-Equivalence-Relation)

open Large-Equivalence-Relation public
```
