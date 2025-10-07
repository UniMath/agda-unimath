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
open import foundation.universe-levels

open import order-theory.large-preorders
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
    (α : Level → Level) (β : Level → Level → Level) : UUω
  where

  constructor
    make-Large-Equivalence-Relation

  field
    large-preorder-Large-Equivalence-Relation :
      Large-Preorder α β

  type-Large-Equivalence-Relation : (l : Level) → UU (α l)
  type-Large-Equivalence-Relation =
    type-Large-Preorder large-preorder-Large-Equivalence-Relation

  prop-Large-Equivalence-Relation :
    {l1 l2 : Level} →
    type-Large-Equivalence-Relation l1 → type-Large-Equivalence-Relation l2 →
    Prop (β l1 l2)
  prop-Large-Equivalence-Relation =
    leq-prop-Large-Preorder large-preorder-Large-Equivalence-Relation

  sim-Large-Equivalence-Relation :
    {l1 l2 : Level} →
    type-Large-Equivalence-Relation l1 → type-Large-Equivalence-Relation l2 →
    UU (β l1 l2)
  sim-Large-Equivalence-Relation x y =
    type-Prop (prop-Large-Equivalence-Relation x y)

  field
    symmetric-sim-Large-Equivalence-Relation :
      is-symmetric-Large-Relation
        ( type-Large-Equivalence-Relation)
        ( sim-Large-Equivalence-Relation)

  refl-sim-Large-Equivalence-Relation :
    is-reflexive-Large-Relation
      ( type-Large-Equivalence-Relation)
      ( sim-Large-Equivalence-Relation)
  refl-sim-Large-Equivalence-Relation =
    refl-leq-Large-Preorder large-preorder-Large-Equivalence-Relation

  transitive-sim-Large-Equivalence-Relation :
    is-transitive-Large-Relation
      ( type-Large-Equivalence-Relation)
      ( sim-Large-Equivalence-Relation)
  transitive-sim-Large-Equivalence-Relation =
    transitive-leq-Large-Preorder large-preorder-Large-Equivalence-Relation

  sim-eq-Large-Equivalence-Relation :
    {l : Level} {x y : type-Large-Equivalence-Relation l} →
    x ＝ y → sim-Large-Equivalence-Relation x y
  sim-eq-Large-Equivalence-Relation =
    leq-eq-Large-Preorder (large-preorder-Large-Equivalence-Relation)

  equivalence-relation-Large-Equivalence-Relation :
    (l : Level) →
    equivalence-relation (β l l) (type-Large-Equivalence-Relation l)
  equivalence-relation-Large-Equivalence-Relation l =
    ( prop-Large-Equivalence-Relation ,
      refl-sim-Large-Equivalence-Relation ,
      symmetric-sim-Large-Equivalence-Relation ,
      transitive-sim-Large-Equivalence-Relation)

open Large-Equivalence-Relation public
```
