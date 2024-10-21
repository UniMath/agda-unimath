# Pullbacks of dependent reflexive graphs

```agda
module graph-theory.pullbacks-dependent-reflexive-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import graph-theory.dependent-directed-graphs
open import graph-theory.dependent-reflexive-graphs
open import graph-theory.morphisms-reflexive-graphs
open import graph-theory.pullbacks-dependent-directed-graphs
open import graph-theory.reflexive-graphs
```

</details>

## Idea

Consider a
[dependent reflexive graph](graph-theory.dependent-reflexive-graphs.md) `B` over
a [reflexive graph](graph-theory.reflexive-graphs.md) `A`, and consider a
[graph homomorphism](graph-theory.morphisms-reflexive-graphs.md) `f : C → A`.
The {{#concept "pullback" Disambiguation="dependent reflexive graphs"}} `f*B` of
`B` along `f` is defined by substituting the values of `f` into `B`. More
precisely, `f*B` is defined by

```text
  (f*B)₀ c := B₀ (f₀ c)
  (f*B)₁ e := B₁ (f₁ e).
```

## Definitions

### The pullback of dependent reflexive graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : Reflexive-Graph l1 l2}
  (C : Reflexive-Graph l3 l4) (f : hom-Reflexive-Graph C A)
  (B : Dependent-Reflexive-Graph l5 l6 A)
  where

  dependent-directed-graph-pullback-Dependent-Reflexive-Graph :
    Dependent-Directed-Graph l5 l6 (directed-graph-Reflexive-Graph C)
  dependent-directed-graph-pullback-Dependent-Reflexive-Graph =
    pullback-Dependent-Directed-Graph
      ( directed-graph-Reflexive-Graph C)
      ( hom-directed-graph-hom-Reflexive-Graph C A f)
      ( dependent-directed-graph-Dependent-Reflexive-Graph B)

  vertex-pullback-Dependent-Reflexive-Graph :
    (x : vertex-Reflexive-Graph C) → UU l5
  vertex-pullback-Dependent-Reflexive-Graph =
    vertex-Dependent-Directed-Graph
      dependent-directed-graph-pullback-Dependent-Reflexive-Graph

  edge-pullback-Dependent-Reflexive-Graph :
    {x y : vertex-Reflexive-Graph C} (e : edge-Reflexive-Graph C x y) →
    vertex-pullback-Dependent-Reflexive-Graph x →
    vertex-pullback-Dependent-Reflexive-Graph y → UU l6
  edge-pullback-Dependent-Reflexive-Graph =
    edge-Dependent-Directed-Graph
      dependent-directed-graph-pullback-Dependent-Reflexive-Graph

  refl-pullback-Dependent-Reflexive-Graph :
    {x : vertex-Reflexive-Graph C}
    (y : vertex-pullback-Dependent-Reflexive-Graph x) →
    edge-pullback-Dependent-Reflexive-Graph (refl-Reflexive-Graph C x) y y
  refl-pullback-Dependent-Reflexive-Graph {x} y =
    tr
      ( λ u → edge-Dependent-Reflexive-Graph B u y y)
      ( inv (refl-hom-Reflexive-Graph C A f x))
      ( refl-Dependent-Reflexive-Graph B y)
```
