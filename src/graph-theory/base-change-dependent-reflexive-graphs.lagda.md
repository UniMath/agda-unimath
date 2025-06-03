# Base change of dependent reflexive graphs

```agda
module graph-theory.base-change-dependent-reflexive-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import graph-theory.base-change-dependent-directed-graphs
open import graph-theory.dependent-directed-graphs
open import graph-theory.dependent-reflexive-graphs
open import graph-theory.morphisms-reflexive-graphs
open import graph-theory.reflexive-graphs
```

</details>

## Idea

Consider a
[dependent reflexive graph](graph-theory.dependent-reflexive-graphs.md) `B` over
a [reflexive graph](graph-theory.reflexive-graphs.md) `A`, and consider a
[graph homomorphism](graph-theory.morphisms-reflexive-graphs.md) `f : C → A`.
The
{{#concept "base change" Disambiguation="dependent reflexive graphs" Agda=base-change-Dependent-Reflexive-Graph}}
`f*B` of `B` along `f` is defined by substituting the values of `f` into `B`.
More precisely, `f*B` is defined by

```text
  (f*B)₀ c := B₀ (f₀ c)
  (f*B)₁ e := B₁ (f₁ e).
```

## Definitions

### Base change of dependent reflexive graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : Reflexive-Graph l1 l2}
  (C : Reflexive-Graph l3 l4) (f : hom-Reflexive-Graph C A)
  (B : Dependent-Reflexive-Graph l5 l6 A)
  where

  dependent-directed-graph-base-change-Dependent-Reflexive-Graph :
    Dependent-Directed-Graph l5 l6 (directed-graph-Reflexive-Graph C)
  dependent-directed-graph-base-change-Dependent-Reflexive-Graph =
    base-change-Dependent-Directed-Graph
      ( directed-graph-Reflexive-Graph C)
      ( hom-directed-graph-hom-Reflexive-Graph C A f)
      ( dependent-directed-graph-Dependent-Reflexive-Graph B)

  vertex-base-change-Dependent-Reflexive-Graph :
    (x : vertex-Reflexive-Graph C) → UU l5
  vertex-base-change-Dependent-Reflexive-Graph =
    vertex-Dependent-Directed-Graph
      dependent-directed-graph-base-change-Dependent-Reflexive-Graph

  edge-base-change-Dependent-Reflexive-Graph :
    {x y : vertex-Reflexive-Graph C} (e : edge-Reflexive-Graph C x y) →
    vertex-base-change-Dependent-Reflexive-Graph x →
    vertex-base-change-Dependent-Reflexive-Graph y → UU l6
  edge-base-change-Dependent-Reflexive-Graph =
    edge-Dependent-Directed-Graph
      dependent-directed-graph-base-change-Dependent-Reflexive-Graph

  refl-base-change-Dependent-Reflexive-Graph :
    {x : vertex-Reflexive-Graph C}
    (y : vertex-base-change-Dependent-Reflexive-Graph x) →
    edge-base-change-Dependent-Reflexive-Graph (refl-Reflexive-Graph C x) y y
  refl-base-change-Dependent-Reflexive-Graph {x} y =
    tr
      ( λ u → edge-Dependent-Reflexive-Graph B u y y)
      ( inv (refl-hom-Reflexive-Graph C A f x))
      ( refl-Dependent-Reflexive-Graph B y)

  base-change-Dependent-Reflexive-Graph :
    Dependent-Reflexive-Graph l5 l6 C
  pr1 base-change-Dependent-Reflexive-Graph =
    dependent-directed-graph-base-change-Dependent-Reflexive-Graph
  pr2 base-change-Dependent-Reflexive-Graph _ =
    refl-base-change-Dependent-Reflexive-Graph
```
