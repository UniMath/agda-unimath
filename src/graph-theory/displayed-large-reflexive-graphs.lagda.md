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

A
{{#concept "displayed large reflexive graph" Agda=Displayed-Large-Reflexive-Graph}}
`H` a over a base
[large reflexive graph](graph-theory.large-reflexive-graphs.md) `G` is the
[structure](foundation.structure.md) of a dependent large reflexive graph over
`G`. It consists of

- A family of vertices over the vertices of `G`.
- A family of dependent edges over the edges of `G`. More concretely, for every
  edge `e : x → y` in `G` and `x'` in `H` over `x`, and `y'` over `x`, a type of
  _edges from `x'` to `y'` over `e`_:

  ```text
    x' ·········> y'   ∋ H

           ↧

    x ----------> y    ∋ G.
           e
  ```

- A family of reflexivity edges `refl : x' → x'` over every reflexivity edge in
  `G`.

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
  {G : Large-Reflexive-Graph α1 β1}
  (H : Displayed-Large-Reflexive-Graph α2 β2 G)
  where

  vertex-total-large-reflexive-graph-Displayed-Large-Reflexive-Graph :
    (l : Level) → UU (α1 l ⊔ α2 l)
  vertex-total-large-reflexive-graph-Displayed-Large-Reflexive-Graph l =
    Σ ( vertex-Large-Reflexive-Graph G l)
      ( vertex-Displayed-Large-Reflexive-Graph H)

  edge-total-large-reflexive-graph-Displayed-Large-Reflexive-Graph :
    {l1 l2 : Level} →
    vertex-total-large-reflexive-graph-Displayed-Large-Reflexive-Graph l1 →
    vertex-total-large-reflexive-graph-Displayed-Large-Reflexive-Graph l2 →
    UU (β1 l1 l2 ⊔ β2 l1 l2)
  edge-total-large-reflexive-graph-Displayed-Large-Reflexive-Graph
    ( x , x') (y , y') =
    Σ ( edge-Large-Reflexive-Graph G x y)
      ( λ e → edge-Displayed-Large-Reflexive-Graph H e x' y')

  refl-total-large-reflexive-graph-Displayed-Large-Reflexive-Graph :
    {l : Level}
    (x : vertex-total-large-reflexive-graph-Displayed-Large-Reflexive-Graph l) →
    edge-total-large-reflexive-graph-Displayed-Large-Reflexive-Graph x x
  refl-total-large-reflexive-graph-Displayed-Large-Reflexive-Graph (x , x') =
    ( refl-Large-Reflexive-Graph G x ,
      refl-Displayed-Large-Reflexive-Graph H x')

  total-large-reflexive-graph-Displayed-Large-Reflexive-Graph :
    Large-Reflexive-Graph (λ l → α1 l ⊔ α2 l) (λ l1 l2 → β1 l1 l2 ⊔ β2 l1 l2)
  vertex-Large-Reflexive-Graph
    total-large-reflexive-graph-Displayed-Large-Reflexive-Graph =
      vertex-total-large-reflexive-graph-Displayed-Large-Reflexive-Graph
  edge-Large-Reflexive-Graph
    total-large-reflexive-graph-Displayed-Large-Reflexive-Graph =
    edge-total-large-reflexive-graph-Displayed-Large-Reflexive-Graph
  refl-Large-Reflexive-Graph
    total-large-reflexive-graph-Displayed-Large-Reflexive-Graph =
    refl-total-large-reflexive-graph-Displayed-Large-Reflexive-Graph
```

### The fiber reflexive graph of a displayed large reflexive graph over a vertex

```agda
module _
  {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level}
  {G : Large-Reflexive-Graph α1 β1}
  (H : Displayed-Large-Reflexive-Graph α2 β2 G)
  {l : Level} (x : vertex-Large-Reflexive-Graph G l)
  where

  fiber-vertex-reflexive-graph-Displayed-Large-Reflexive-Graph :
    Reflexive-Graph (α2 l) (β2 l l)
  pr1 (pr1 fiber-vertex-reflexive-graph-Displayed-Large-Reflexive-Graph) =
    vertex-Displayed-Large-Reflexive-Graph H x
  pr2 (pr1 fiber-vertex-reflexive-graph-Displayed-Large-Reflexive-Graph) =
    edge-Displayed-Large-Reflexive-Graph H (refl-Large-Reflexive-Graph G x)
  pr2 fiber-vertex-reflexive-graph-Displayed-Large-Reflexive-Graph =
    refl-Displayed-Large-Reflexive-Graph H
```
