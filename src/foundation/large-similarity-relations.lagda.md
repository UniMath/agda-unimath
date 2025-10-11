# Large similarity relations

```agda
module foundation.large-similarity-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.large-equivalence-relations
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "large similarity relation" Agda=Large-Similarity-Relation}} is a
[propositionally](foundation.propositions.md) valued
[large equivalence relation](foundation.large-equivalence-relations.md) that is
[antisymmetric](foundation.large-binary-relations.md), or equivalently, where
similarity at the same [universe level](foundation.universe-levels.md) implies
[equality](foundation.identity-types.md).

## Definition

```agda
record
  Large-Similarity-Relation
    {α : Level → Level} (β : Level → Level → Level)
    (X : (l : Level) → UU (α l)) : UUω
  where

  constructor
    make-Large-Similarity-Relation

  field
    large-equivalence-relation-Large-Similarity-Relation :
      Large-Equivalence-Relation β X

  sim-prop-Large-Similarity-Relation : Large-Relation-Prop β X
  sim-prop-Large-Similarity-Relation =
    sim-prop-Large-Equivalence-Relation
      ( large-equivalence-relation-Large-Similarity-Relation)

  sim-Large-Similarity-Relation : Large-Relation β X
  sim-Large-Similarity-Relation x y =
    type-Prop (sim-prop-Large-Similarity-Relation x y)

  field
    eq-sim-Large-Similarity-Relation :
      {l : Level} → (x y : X l) → sim-Large-Similarity-Relation x y → x ＝ y

  sim-eq-Large-Similarity-Relation :
    {l : Level} {x y : X l} → x ＝ y → sim-Large-Similarity-Relation x y
  sim-eq-Large-Similarity-Relation =
    sim-eq-Large-Equivalence-Relation
      ( large-equivalence-relation-Large-Similarity-Relation)

  refl-sim-Large-Similarity-Relation :
    is-reflexive-Large-Relation-Prop X sim-prop-Large-Similarity-Relation
  refl-sim-Large-Similarity-Relation =
    refl-sim-Large-Equivalence-Relation
      ( large-equivalence-relation-Large-Similarity-Relation)

  symmetric-sim-Large-Similarity-Relation :
    is-symmetric-Large-Relation-Prop X sim-prop-Large-Similarity-Relation
  symmetric-sim-Large-Similarity-Relation =
    symmetric-sim-Large-Equivalence-Relation
      ( large-equivalence-relation-Large-Similarity-Relation)

  transitive-sim-Large-Similarity-Relation :
    is-transitive-Large-Relation-Prop X sim-prop-Large-Similarity-Relation
  transitive-sim-Large-Similarity-Relation =
    transitive-sim-Large-Equivalence-Relation
      ( large-equivalence-relation-Large-Similarity-Relation)

open Large-Similarity-Relation public
```
