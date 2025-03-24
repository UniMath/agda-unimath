# Discrete reflexive graphs

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module graph-theory.discrete-reflexive-graphs
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types funext univalence
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types funext
open import foundation.discrete-reflexive-relations funext univalence truncations
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.torsorial-type-families

open import graph-theory.directed-graphs funext univalence
open import graph-theory.reflexive-graphs funext univalence truncations
```

</details>

## Idea

A [reflexive graph](graph-theory.reflexive-graphs.md) `G ≐ (V , E , r)` is said
to be
{{#concept "discrete" Disambiguation="reflexive graph" Agda=is-discrete-Reflexive-Graph}}
if, for every vertex `x : V`, the type family of edges with source `x`, `E x`,
is [torsorial](foundation-core.torsorial-type-families.md). In other words, if
the [dependent sum](foundation.dependent-pair-types.md) `Σ (y : V), (E x y)` is
[contractible](foundation-core.contractible-types.md) for every `x`. The
{{#concept "standard discrete graph"}} associated to a type `X` is the reflexive
graph whose vertices are elements of `X`, and edges are
[identifications](foundation-core.identity-types.md),

```text
  E x y := (x ＝ y).
```

For any type `A` there is a
{{#concept "standard discrete reflexive graph" Agda=standard-Discrete-Reflexive-Graph}}
`Δ A`, which is defined by

```text
  (Δ A)₀ := A
  (Δ A)₁ := Id A
  refl (Δ A) := refl
```

Since torsorial type families are
[identity systems](foundation.identity-systems.md), it follows that a reflexive
graph is discrete precisely when its edge relation is initial. In other words,
the inclusion of the discrete reflexive graphs into the reflexive graphs
satisfies the universal property of being left adjoint to the forgetful functor
`G ↦ Δ G₀`, mapping a reflexive graph to the standard discrete graph on its type
of vertices.

## Definitions

### The predicate on reflexive graphs of being discrete

```agda
module _
  {l1 l2 : Level} (G : Reflexive-Graph l1 l2)
  where

  is-discrete-prop-Reflexive-Graph : Prop (l1 ⊔ l2)
  is-discrete-prop-Reflexive-Graph =
    is-discrete-prop-Reflexive-Relation
      ( edge-reflexive-relation-Reflexive-Graph G)

  is-discrete-Reflexive-Graph : UU (l1 ⊔ l2)
  is-discrete-Reflexive-Graph =
    type-Prop is-discrete-prop-Reflexive-Graph

  is-prop-is-discrete-Reflexive-Graph : is-prop is-discrete-Reflexive-Graph
  is-prop-is-discrete-Reflexive-Graph =
    is-prop-type-Prop is-discrete-prop-Reflexive-Graph
```

### Discrete reflexive graphs

```agda
module _
  (l1 l2 : Level)
  where

  Discrete-Reflexive-Graph : UU (lsuc l1 ⊔ lsuc l2)
  Discrete-Reflexive-Graph =
    Σ (Reflexive-Graph l1 l2) is-discrete-Reflexive-Graph
```

### The standard discrete reflexive graph

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  discrete-Reflexive-Graph : Reflexive-Graph l1 l1
  pr1 (pr1 discrete-Reflexive-Graph) = A
  pr2 (pr1 discrete-Reflexive-Graph) = Id
  pr2 discrete-Reflexive-Graph x = refl

  is-discrete-discrete-Reflexive-Graph :
    is-discrete-Reflexive-Graph discrete-Reflexive-Graph
  is-discrete-discrete-Reflexive-Graph =
    is-torsorial-Id

  standard-Discrete-Reflexive-Graph :
    Discrete-Reflexive-Graph l1 l1
  pr1 standard-Discrete-Reflexive-Graph = discrete-Reflexive-Graph
  pr2 standard-Discrete-Reflexive-Graph = is-discrete-discrete-Reflexive-Graph
```

## See also

- [Discrete directed graphs](graph-theory.discrete-directed-graphs.md)
- [Discrete dependent reflexive graphs](graph-theory.discrete-dependent-reflexive-graphs.md)
