# Discrete types

```agda
module foundation.discrete-types where

open import foundation-core.discrete-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.binary-relations
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.tight-apartness-relations
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

A {{#concept "discrete type"}} is a type that has
[decidable equality](foundation.decidable-equality.md). Consequently, discrete
types are [sets](foundation-core.sets.md) by Hedberg's theorem.

## Properties

### The apartness relation on a discrete type is negated equality

```agda
module _
  {l : Level} (X : Discrete-Type l)
  where

  rel-apart-Discrete-Type : Relation-Prop l (type-Discrete-Type X)
  rel-apart-Discrete-Type x y = neg-type-Prop (x ＝ y)

  apart-Discrete-Type : (x y : type-Discrete-Type X) → UU l
  apart-Discrete-Type x y = type-Prop (rel-apart-Discrete-Type x y)

  antireflexive-apart-Discrete-Type : is-antireflexive rel-apart-Discrete-Type
  antireflexive-apart-Discrete-Type x r = r refl

  symmetric-apart-Discrete-Type : is-symmetric apart-Discrete-Type
  symmetric-apart-Discrete-Type x y H p = H (inv p)

  cotransitive-apart-Discrete-Type : is-cotransitive rel-apart-Discrete-Type
  cotransitive-apart-Discrete-Type x y z r
    with has-decidable-equality-type-Discrete-Type X x y
  ... | inl refl = unit-trunc-Prop (inr (λ s → r s))
  ... | inr np = unit-trunc-Prop (inl np)

  is-tight-apart-Discrete-Type :
    is-tight rel-apart-Discrete-Type
  is-tight-apart-Discrete-Type x y =
    double-negation-elim-is-decidable
      ( has-decidable-equality-type-Discrete-Type X x y)

  apartness-relation-Discrete-Type :
    Apartness-Relation l (type-Discrete-Type X)
  pr1 apartness-relation-Discrete-Type = rel-apart-Discrete-Type
  pr1 (pr2 apartness-relation-Discrete-Type) = antireflexive-apart-Discrete-Type
  pr1 (pr2 (pr2 apartness-relation-Discrete-Type)) =
    symmetric-apart-Discrete-Type
  pr2 (pr2 (pr2 apartness-relation-Discrete-Type)) =
    cotransitive-apart-Discrete-Type

  type-with-apartness-Discrete-Type : Type-With-Apartness l l
  pr1 type-with-apartness-Discrete-Type = type-Discrete-Type X
  pr2 type-with-apartness-Discrete-Type = apartness-relation-Discrete-Type

  tight-apartness-relation-Discrete-Type :
    Tight-Apartness-Relation l (type-Discrete-Type X)
  pr1 tight-apartness-relation-Discrete-Type =
    apartness-relation-Discrete-Type
  pr2 tight-apartness-relation-Discrete-Type =
    is-tight-apart-Discrete-Type

  type-with-tight-apartness-Discrete-Type : Type-With-Tight-Apartness l l
  pr1 type-with-tight-apartness-Discrete-Type =
    type-with-apartness-Discrete-Type
  pr2 type-with-tight-apartness-Discrete-Type =
    is-tight-apart-Discrete-Type
```

## External links

- [classical set](https://ncatlab.org/nlab/show/classical+set) at $n$Lab
- [decidable object](https://ncatlab.org/nlab/show/decidable+object) at $n$Lab
