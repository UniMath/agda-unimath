# Base change of dependent directed graphs

```agda
module graph-theory.base-change-dependent-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import graph-theory.dependent-directed-graphs
open import graph-theory.directed-graphs
open import graph-theory.morphisms-directed-graphs
```

</details>

## Idea

Consider a [dependent directed graph](graph-theory.dependent-directed-graphs.md)
`B` over a [directed graph](graph-theory.directed-graphs.md) `A`, and consider a
[graph homomorphism](graph-theory.morphisms-directed-graphs.md) `f : C → A`. The
{{#concept "base change" Disambiguation="dependent directed graphs" Agda=base-change-Dependent-Directed-Graph}}
`f*B` of `B` along `f` is defined by substituting the values of `f` into `B`.
More precisely, `f*B` is defined by

```text
  (f*B)₀ c := B₀ (f₀ c)
  (f*B)₁ e := B₁ (f₁ e).
```

## Definitions

### Base change of dependent directed graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : Directed-Graph l1 l2}
  (C : Directed-Graph l3 l4) (f : hom-Directed-Graph C A)
  (B : Dependent-Directed-Graph l5 l6 A)
  where

  vertex-base-change-Dependent-Directed-Graph :
    (c : vertex-Directed-Graph C) → UU l5
  vertex-base-change-Dependent-Directed-Graph c =
    vertex-Dependent-Directed-Graph B (vertex-hom-Directed-Graph C A f c)

  edge-base-change-Dependent-Directed-Graph :
    {x y : vertex-Directed-Graph C} (e : edge-Directed-Graph C x y) →
    vertex-base-change-Dependent-Directed-Graph x →
    vertex-base-change-Dependent-Directed-Graph y → UU l6
  edge-base-change-Dependent-Directed-Graph e =
    edge-Dependent-Directed-Graph B (edge-hom-Directed-Graph C A f e)

  base-change-Dependent-Directed-Graph :
    Dependent-Directed-Graph l5 l6 C
  pr1 base-change-Dependent-Directed-Graph =
    vertex-base-change-Dependent-Directed-Graph
  pr2 base-change-Dependent-Directed-Graph _ _ =
    edge-base-change-Dependent-Directed-Graph
```
