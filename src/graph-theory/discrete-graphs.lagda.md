# Discrete graphs

```agda
module graph-theory.discrete-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.torsorial-type-families

open import graph-theory.reflexive-graphs
```

</details>

## Idea

A [reflexive graph](graph-theory.reflexive-graphs.md) `G = (V , E)` is said to
be
{{#concept "discrete" Disambiguation="reflexive graph" Agda=is-discrete-Reflexive-Graph}}
if, for every vertex `x`, the type family of edges with source `x`, `E x`, is
[torsorial](foundation-core.torsorial-type-families.md). In other words, the
[dependent sum](foundation.dependent-pair-types.md) `Σ (y : V), (E x y)` is
[contractible](foundation-core.contractible-types.md) for every `x`. The
{{#concept "standard discrete
graph" Agda=Id-Reflexive-Graph}} associated to a type `X` is the graph whose vertices
are elements of `X`, and edges are [identifications](foundation-core.identity-types.md).

## Definitions

### The predicate on reflexive graphs of being discrete

```agda
module _
  {l1 l2 : Level} (R : Reflexive-Graph l1 l2)
  where

  is-discrete-Reflexive-Graph-Prop : Prop (l1 ⊔ l2)
  is-discrete-Reflexive-Graph-Prop =
    Π-Prop
      ( vertex-Reflexive-Graph R)
      ( λ x →
        is-contr-Prop (Σ (vertex-Reflexive-Graph R) (edge-Reflexive-Graph R x)))

  is-discrete-Reflexive-Graph : UU (l1 ⊔ l2)
  is-discrete-Reflexive-Graph =
    type-Prop is-discrete-Reflexive-Graph-Prop

  is-prop-is-discrete-Reflexive-Graph : is-prop is-discrete-Reflexive-Graph
  is-prop-is-discrete-Reflexive-Graph =
    is-prop-type-Prop is-discrete-Reflexive-Graph-Prop
```

### The standard discrete graph associated to a type

```agda
module _
  {l : Level} (A : UU l)
  where

  Id-Reflexive-Graph : Reflexive-Graph l l
  Id-Reflexive-Graph = (A , Id , (λ x → refl))

  is-discrete-Id-Reflexive-Graph :
    is-discrete-Reflexive-Graph Id-Reflexive-Graph
  is-discrete-Id-Reflexive-Graph = is-torsorial-Id
```
