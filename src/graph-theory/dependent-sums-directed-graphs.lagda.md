# Dependent sums directed graphs

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module graph-theory.dependent-sums-directed-graphs
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import graph-theory.base-change-dependent-directed-graphs funext univalence truncations
open import graph-theory.dependent-directed-graphs funext univalence
open import graph-theory.directed-graphs funext univalence
open import graph-theory.morphisms-directed-graphs funext univalence truncations
open import graph-theory.sections-dependent-directed-graphs funext univalence truncations
```

</details>

## Idea

Consider a [dependent directed graph](graph-theory.dependent-directed-graphs.md)
`H` over a [directed graph](graph-theory.directed-graphs.md) `G`. The
{{#concept "dependent sum" Disambiguation="directed graphs" Agda=Σ-Directed-Graph}}
`Σ G H` is the directed graph given by

```text
  (Σ G H)₀ := Σ G₀ H₀
  (Σ G H)₁ (x , y) (x' , y') := Σ (e : G₁ x x') (H₁ e y y').
```

## Definitions

### The dependent sum of directed graphs

```agda
module _
  {l1 l2 l3 l4 : Level} {G : Directed-Graph l1 l2}
  (H : Dependent-Directed-Graph l3 l4 G)
  where

  vertex-Σ-Directed-Graph : UU (l1 ⊔ l3)
  vertex-Σ-Directed-Graph =
    Σ (vertex-Directed-Graph G) (vertex-Dependent-Directed-Graph H)

  edge-Σ-Directed-Graph :
    (x y : vertex-Σ-Directed-Graph) → UU (l2 ⊔ l4)
  edge-Σ-Directed-Graph (x , y) (x' , y') =
    Σ ( edge-Directed-Graph G x x')
      ( λ e → edge-Dependent-Directed-Graph H e y y')

  Σ-Directed-Graph : Directed-Graph (l1 ⊔ l3) (l2 ⊔ l4)
  pr1 Σ-Directed-Graph = vertex-Σ-Directed-Graph
  pr2 Σ-Directed-Graph = edge-Σ-Directed-Graph
```

### The first projection of the dependent sums of directed graph

```agda
module _
  {l1 l2 l3 l4 : Level} {G : Directed-Graph l1 l2}
  (H : Dependent-Directed-Graph l3 l4 G)
  where

  vertex-pr1-Σ-Directed-Graph :
    vertex-Σ-Directed-Graph H → vertex-Directed-Graph G
  vertex-pr1-Σ-Directed-Graph = pr1

  edge-pr1-Σ-Directed-Graph :
    {x y : vertex-Σ-Directed-Graph H} →
    edge-Σ-Directed-Graph H x y →
    edge-Directed-Graph G
      ( vertex-pr1-Σ-Directed-Graph x)
      ( vertex-pr1-Σ-Directed-Graph y)
  edge-pr1-Σ-Directed-Graph = pr1

  pr1-Σ-Directed-Graph :
    hom-Directed-Graph (Σ-Directed-Graph H) G
  pr1 pr1-Σ-Directed-Graph = vertex-pr1-Σ-Directed-Graph
  pr2 pr1-Σ-Directed-Graph _ _ = edge-pr1-Σ-Directed-Graph
```

### The second projection of the dependent sums of directed graph

```agda
module _
  {l1 l2 l3 l4 : Level} {G : Directed-Graph l1 l2}
  (H : Dependent-Directed-Graph l3 l4 G)
  where

  vertex-pr2-Σ-Directed-Graph :
    (x : vertex-Σ-Directed-Graph H) →
    vertex-Dependent-Directed-Graph H (vertex-pr1-Σ-Directed-Graph H x)
  vertex-pr2-Σ-Directed-Graph = pr2

  edge-pr2-Σ-Directed-Graph :
    {x y : vertex-Σ-Directed-Graph H}
    (e : edge-Σ-Directed-Graph H x y) →
    edge-Dependent-Directed-Graph H
      ( edge-pr1-Σ-Directed-Graph H e)
      ( vertex-pr2-Σ-Directed-Graph x)
      ( vertex-pr2-Σ-Directed-Graph y)
  edge-pr2-Σ-Directed-Graph = pr2

  pr2-Σ-Directed-Graph :
    section-Dependent-Directed-Graph
      ( base-change-Dependent-Directed-Graph
        ( Σ-Directed-Graph H)
        ( pr1-Σ-Directed-Graph H)
        ( H))
  pr1 pr2-Σ-Directed-Graph = vertex-pr2-Σ-Directed-Graph
  pr2 pr2-Σ-Directed-Graph = edge-pr2-Σ-Directed-Graph
```

## See also

- [Dependent product directed graphs](graph-theory.dependent-products-directed-graphs.md)
