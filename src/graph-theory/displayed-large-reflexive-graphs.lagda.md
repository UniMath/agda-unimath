# Displayed large reflexive graphs

```agda
module graph-theory.displayed-large-reflexive-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import graph-theory.large-reflexive-graphs
open import graph-theory.reflexive-graphs
```

</details>

## Idea

A {{#concept "displayed large reflexive graph"}} is a dependent reflexive graph
over a base reflexive graph `G`.

## Definitions

### Displayed large reflexive graphs

```agda
record
  Displayed-Large-Reflexive-Graph
  {α' : Level → Level} {β' : Level → Level → Level}
  (α : Level → Level) (β : Level → Level → Level)
  (G : Large-Reflexive-Graph α' β') : UUω
  where

  field
    vertex-Displayed-Large-Reflexive-Graph :
      {l : Level} (x : vertex-Large-Reflexive-Graph G l) → UU (α l)

    edge-Displayed-Large-Reflexive-Graph :
      {l1 l2 : Level}
      {x : vertex-Large-Reflexive-Graph G l1}
      {y : vertex-Large-Reflexive-Graph G l2}
      (f : edge-Large-Reflexive-Graph G x y)
      (x' : vertex-Displayed-Large-Reflexive-Graph x)
      (y' : vertex-Displayed-Large-Reflexive-Graph y) →
      UU (β l1 l2)

    refl-Displayed-Large-Reflexive-Graph :
      {l : Level}
      {x : vertex-Large-Reflexive-Graph G l}
      (x' : vertex-Displayed-Large-Reflexive-Graph x) →
      edge-Displayed-Large-Reflexive-Graph
        ( refl-Large-Reflexive-Graph G x)
        ( x')
        ( x')

open Displayed-Large-Reflexive-Graph public
```

### The total large reflexive graph of a displayed large reflexive graph

```agda
module _
  {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level}
  (G : Large-Reflexive-Graph α1 β1)
  (H : Displayed-Large-Reflexive-Graph α2 β2 G)
  where

  total-large-reflexive-graph-Displayed-Large-Reflexive-Graph :
    Large-Reflexive-Graph (λ l → α1 l ⊔ α2 l) (λ l1 l2 → β1 l1 l2 ⊔ β2 l1 l2)
  vertex-Large-Reflexive-Graph
    total-large-reflexive-graph-Displayed-Large-Reflexive-Graph l =
      Σ ( vertex-Large-Reflexive-Graph G l)
        ( vertex-Displayed-Large-Reflexive-Graph H)
  edge-Large-Reflexive-Graph
    total-large-reflexive-graph-Displayed-Large-Reflexive-Graph
    ( x , x') (y , y') =
    Σ ( edge-Large-Reflexive-Graph G x y)
      ( λ e → edge-Displayed-Large-Reflexive-Graph H e x' y')
  refl-Large-Reflexive-Graph
    total-large-reflexive-graph-Displayed-Large-Reflexive-Graph
    ( x , x') =
    ( refl-Large-Reflexive-Graph G x ,
      refl-Displayed-Large-Reflexive-Graph H x')
```

### The fiber reflexive graph of a displayed large reflexive graph over a vertex

```agda
module _
  {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level}
  (G : Large-Reflexive-Graph α1 β1)
  (H : Displayed-Large-Reflexive-Graph α2 β2 G)
  {l : Level} (x : vertex-Large-Reflexive-Graph G l)
  where

  fiber-reflexive-graph-Displayed-Large-Reflexive-Graph :
    Reflexive-Graph (α2 l) (β2 l l)
  pr1 fiber-reflexive-graph-Displayed-Large-Reflexive-Graph =
    vertex-Displayed-Large-Reflexive-Graph H x
  pr1 (pr2 fiber-reflexive-graph-Displayed-Large-Reflexive-Graph) =
    edge-Displayed-Large-Reflexive-Graph H (refl-Large-Reflexive-Graph G x)
  pr2 (pr2 fiber-reflexive-graph-Displayed-Large-Reflexive-Graph) =
    refl-Displayed-Large-Reflexive-Graph H
```
