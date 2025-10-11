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

## Properties

### Similarity reasoning

Large similarity relations can be equationally reasoned in the following way:

```text
let
  open similarity-reasoning-Large-Similarity-Relation S
in
  similarity-reasoning
    x ~ y by sim-1
      ~ z by sim-2
```

```agda
module
  similarity-reasoning-Large-Similarity-Relation
    {α : Level → Level} {β : Level → Level → Level} {X : (l : Level) → UU (α l)}
    (S : Large-Similarity-Relation β X)
  where

  infixl 1 similarity-reasoning_
  infixl 0 step-similarity-reasoning

  abstract
    similarity-reasoning_ :
      {l : Level} → (x : X l) → sim-Large-Similarity-Relation S x x
    similarity-reasoning x = refl-sim-Large-Similarity-Relation S x

    step-similarity-reasoning :
      {l1 l2 : Level} {x : X l1} {y : X l2} →
      sim-Large-Similarity-Relation S x y →
      {l3 : Level} → (u : X l3) → sim-Large-Similarity-Relation S y u →
      sim-Large-Similarity-Relation S x u
    step-similarity-reasoning {x = x} {y = y} p u q =
      transitive-sim-Large-Similarity-Relation S x y u q p

  syntax step-similarity-reasoning p u q = p ~ u by q
```
