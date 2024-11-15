# Discrete directed graphs

```agda
module graph-theory.discrete-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.discrete-binary-relations
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.torsorial-type-families

open import graph-theory.directed-graphs
open import graph-theory.reflexive-graphs
```

</details>

## Idea

A [directed graph](graph-theory.directed-graphs.md) `G ≐ (V , E)` is said to be
{{#concept "discrete" Disambiguation="directed graph" Agda=is-discrete-Directed-Graph}}
if it has no edges. In other words, a directed graph is discrete if it is of the
form `Δ A`, where `Δ` is the left adjoint to the forgetful functor `(V , E) ↦ V`
from directed graphs to types.

Recall that [reflexive graphs](graph-theory.reflexive-graphs.md) are said to be
discrete if the edge relation is
[torsorial](foundation-core.torsorial-type-families.md). The condition that a
directed graph is discrete compares to the condition that a reflexive graph is
discrete in the sense that in both cases discreteness implies initiality of the
edge relation: The empty relation is the initial relation, while the identity
relation is the initial reflexive relation.

One may wonder if the torsoriality condition of discreteness shouldn't directly
carry over to the discreteness condition on directed graphs. Indeed, an earlier
implementation of discreteness in agda-unimath had this faulty definition.
However, this leads to examples that are not typically considered discrete.
Consider, for example, the directed graph with `V := ℕ` the
[natural numbers](elementary-number-theory.natural-numbers.md) and
`E m n := (m + 1 ＝ n)` as in

```text
  0 ---> 1 ---> 2 ---> ⋯.
```

This directed graph satisfies the condition that the type family `E m` is
torsorial for every `m : ℕ`, simply because `E` is a
[functional correspondence](foundation.functional-correspondences.md). However,
this graph is not considered discrete since it relates distinct vertices.

## Definitions

### The predicate on graphs of being discrete

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  is-discrete-prop-Directed-Graph : Prop (l1 ⊔ l2)
  is-discrete-prop-Directed-Graph =
    is-discrete-prop-Relation (edge-Directed-Graph G)

  is-discrete-Directed-Graph : UU (l1 ⊔ l2)
  is-discrete-Directed-Graph =
    is-discrete-Relation (edge-Directed-Graph G)

  is-prop-is-discrete-Directed-Graph :
    is-prop is-discrete-Directed-Graph
  is-prop-is-discrete-Directed-Graph =
    is-prop-is-discrete-Relation (edge-Directed-Graph G)
```

## See also

- [Discrete reflexive graphs](graph-theory.discrete-reflexive-graphs.md)
