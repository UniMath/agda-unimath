# Morphisms of dependent directed graphs

```agda
module graph-theory.morphisms-dependent-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import graph-theory.dependent-directed-graphs
open import graph-theory.directed-graphs
```

</details>

## Idea

Consider two
[dependent directed graphs](graph-theory.dependent-directed-graphs.md) `H` and
`K` over a [directed graph](graph-theory.directed-graphs.md) `G`. A
{{#concept "morphism" Agda=hom-Dependent-Directed-Graph}} of dependent directed
graphs from `H` to `K` consists of a family of maps

```text
  f₀ : {x : G₀} → H₀ x → K₀ x
```

of vertices, and a family of maps

```text
  f₁ : {x y : G₀} (a : G₁ x y) {y : H₀ x} {y' : H₀ x'} → H₁ a y y' → K₁ a (f₀ y) (f₀ y')
```

of edges.

## Definitions

### Morphisms of dependent directed graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} {G : Directed-Graph l1 l2}
  (H : Dependent-Directed-Graph l3 l4 G)
  (K : Dependent-Directed-Graph l5 l6 G)
  where

  hom-Dependent-Directed-Graph : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  hom-Dependent-Directed-Graph =
    Σ ( (x : vertex-Directed-Graph G) →
        vertex-Dependent-Directed-Graph H x →
        vertex-Dependent-Directed-Graph K x)
      ( λ f →
        (x x' : vertex-Directed-Graph G) →
        (a : edge-Directed-Graph G x x') →
        (y : vertex-Dependent-Directed-Graph H x)
        (y' : vertex-Dependent-Directed-Graph H x') →
        edge-Dependent-Directed-Graph H a y y' →
        edge-Dependent-Directed-Graph K a (f x y) (f x' y'))

  vertex-hom-Dependent-Directed-Graph :
    hom-Dependent-Directed-Graph →
    {x : vertex-Directed-Graph G} →
    vertex-Dependent-Directed-Graph H x →
    vertex-Dependent-Directed-Graph K x
  vertex-hom-Dependent-Directed-Graph f = pr1 f _

  edge-hom-Dependent-Directed-Graph :
    (f : hom-Dependent-Directed-Graph) →
    {x x' : vertex-Directed-Graph G}
    (a : edge-Directed-Graph G x x')
    {y : vertex-Dependent-Directed-Graph H x}
    {y' : vertex-Dependent-Directed-Graph H x'} →
    edge-Dependent-Directed-Graph H a y y' →
    edge-Dependent-Directed-Graph K a
      ( vertex-hom-Dependent-Directed-Graph f y)
      ( vertex-hom-Dependent-Directed-Graph f y')
  edge-hom-Dependent-Directed-Graph f a =
    pr2 f _ _ a _ _
```

### The identity morphism of a dependent directed graph

```agda
module _
  {l1 l2 l3 l4 : Level} {G : Directed-Graph l1 l2}
  (H : Dependent-Directed-Graph l3 l4 G)
  where

  vertex-id-hom-Dependent-Directed-Graph :
    {x : vertex-Directed-Graph G} →
    vertex-Dependent-Directed-Graph H x →
    vertex-Dependent-Directed-Graph H x
  vertex-id-hom-Dependent-Directed-Graph = id

  edge-id-hom-Dependent-Directed-Graph :
    {x x' : vertex-Directed-Graph G}
    (a : edge-Directed-Graph G x x')
    (y : vertex-Dependent-Directed-Graph H x)
    (y' : vertex-Dependent-Directed-Graph H x') →
    edge-Dependent-Directed-Graph H a y y' →
    edge-Dependent-Directed-Graph H a
      ( vertex-id-hom-Dependent-Directed-Graph y)
      ( vertex-id-hom-Dependent-Directed-Graph y')
  edge-id-hom-Dependent-Directed-Graph a y y' = id

  id-hom-Dependent-Directed-Graph :
    hom-Dependent-Directed-Graph H H
  pr1 id-hom-Dependent-Directed-Graph _ =
    vertex-id-hom-Dependent-Directed-Graph
  pr2 id-hom-Dependent-Directed-Graph _ _ =
    edge-id-hom-Dependent-Directed-Graph
```
