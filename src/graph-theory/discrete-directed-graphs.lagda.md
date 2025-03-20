# Discrete directed graphs

```agda
open import foundation.function-extensionality-axiom

module
  graph-theory.discrete-directed-graphs
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types funext
open import foundation.dependent-pair-types
open import foundation.discrete-binary-relations funext
open import foundation.empty-types funext
open import foundation.equivalences funext
open import foundation.homotopies funext
open import foundation.retractions funext
open import foundation.sections funext
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.torsorial-type-families

open import graph-theory.directed-graphs funext
open import graph-theory.morphisms-directed-graphs funext
open import graph-theory.reflexive-graphs funext
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

### The standard discrete directed graph

```agda
module _
  {l : Level} (A : UU l)
  where

  discrete-Directed-Graph : Directed-Graph l lzero
  pr1 discrete-Directed-Graph = A
  pr2 discrete-Directed-Graph x y = empty
```

## Properties

### Morphisms from a standard discrete directed graph are maps into vertices

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (G : Directed-Graph l1 l2)
  where

  ev-hom-discrete-Directed-Graph :
    hom-Directed-Graph (discrete-Directed-Graph A) G →
    A → vertex-Directed-Graph G
  ev-hom-discrete-Directed-Graph =
    vertex-hom-Directed-Graph (discrete-Directed-Graph _) G

  map-inv-ev-hom-discrete-Directed-Graph :
    (A → vertex-Directed-Graph G) →
    hom-Directed-Graph (discrete-Directed-Graph A) G
  pr1 (map-inv-ev-hom-discrete-Directed-Graph f) = f
  pr2 (map-inv-ev-hom-discrete-Directed-Graph f) x y ()

  is-section-map-inv-ev-hom-discrete-Directed-Graph :
    is-section
      ( ev-hom-discrete-Directed-Graph)
      ( map-inv-ev-hom-discrete-Directed-Graph)
  is-section-map-inv-ev-hom-discrete-Directed-Graph f = refl

  htpy-is-retraction-map-inv-ev-hom-discrete-Directed-Graph :
    (f : hom-Directed-Graph (discrete-Directed-Graph A) G) →
    htpy-hom-Directed-Graph
      ( discrete-Directed-Graph A)
      ( G)
      ( map-inv-ev-hom-discrete-Directed-Graph
        ( ev-hom-discrete-Directed-Graph f))
      ( f)
  pr1 (htpy-is-retraction-map-inv-ev-hom-discrete-Directed-Graph f) =
    refl-htpy
  pr2 (htpy-is-retraction-map-inv-ev-hom-discrete-Directed-Graph f) x y ()

  is-retraction-map-inv-ev-hom-discrete-Directed-Graph :
    is-retraction
      ( ev-hom-discrete-Directed-Graph)
      ( map-inv-ev-hom-discrete-Directed-Graph)
  is-retraction-map-inv-ev-hom-discrete-Directed-Graph f =
    eq-htpy-hom-Directed-Graph
      ( discrete-Directed-Graph A)
      ( G)
      ( map-inv-ev-hom-discrete-Directed-Graph
        ( ev-hom-discrete-Directed-Graph f))
      ( f)
      ( htpy-is-retraction-map-inv-ev-hom-discrete-Directed-Graph f)

  abstract
    is-equiv-ev-hom-discrete-Directed-Graph :
      is-equiv ev-hom-discrete-Directed-Graph
    is-equiv-ev-hom-discrete-Directed-Graph =
      is-equiv-is-invertible
        map-inv-ev-hom-discrete-Directed-Graph
        is-section-map-inv-ev-hom-discrete-Directed-Graph
        is-retraction-map-inv-ev-hom-discrete-Directed-Graph

  ev-equiv-hom-discrete-Directed-Graph :
    hom-Directed-Graph (discrete-Directed-Graph A) G ≃
    (A → vertex-Directed-Graph G)
  pr1 ev-equiv-hom-discrete-Directed-Graph =
    ev-hom-discrete-Directed-Graph
  pr2 ev-equiv-hom-discrete-Directed-Graph =
    is-equiv-ev-hom-discrete-Directed-Graph
```

## See also

- [Discrete reflexive graphs](graph-theory.discrete-reflexive-graphs.md)
