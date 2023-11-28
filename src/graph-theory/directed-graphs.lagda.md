# Directed graphs

```agda
module graph-theory.directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "directed graph" Agda={Directed-Graph,Directed-Graph'} WD="Directed graph" WDID=Q1137726}}
consists of a type of **vertices** equipped with a
[binary, type valued relation](foundation.binary-relations.md) of **edges**.
Alternatively, one can define a directed graph to consist of a type `V` of
vertices, a type `E` of edges, and a
[pair](foundation-core.cartesian-product-types.md) of maps `s t : E → V`
determining the **source** and **target** of each edge.

To see that these two definitions are
[equivalent](foundation-core.equivalences.md), recall that
[`Σ`-types](foundation.dependent-pair-types.md) preserve equivalences and a type
family `A → 𝒰` is equivalent to `Σ (C : 𝒰), (C → A)` by
[type duality](foundation.type-duality.md). Using these two observations we make
the following calculation:

```text
  Σ (V : 𝒰), (V → V → 𝒰)
  ≃ Σ (V : 𝒰), (V × V → 𝒰)
  ≃ Σ (V E : 𝒰), E → V × V
  ≃ Σ (V E : 𝒰), (E → V) × (E → V)
```

**Remark.** Our definition of directed graph is as general as possible: The
types of vertices and edges are allowed to be arbitrary types. In particular,
they are allowed to be infinite and they are not required to be
[sets](foundation-core.sets.md). Furthermore, we don't require the type of edges
`E v v` from a vertex `v` to itself to be
[empty](foundation-core.empty-types.md). Many concepts in graph theory, such as
the concept of being a [directed tree](trees.directed-trees.md) are definable in
this general setting. For more specific kinds of graphs, such as finite graphs,
simple graphs, or connected graphs, we always fully disambiguate.

## Definition

### Directed graphs (main definition)

```agda
Directed-Graph : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Directed-Graph l1 l2 = Σ (UU l1) (Relation l2)

module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  vertex-Directed-Graph : UU l1
  vertex-Directed-Graph = pr1 G

  edge-Directed-Graph : Relation l2 vertex-Directed-Graph
  edge-Directed-Graph = pr2 G

  total-edge-Directed-Graph : UU (l1 ⊔ l2)
  total-edge-Directed-Graph =
    Σ ( vertex-Directed-Graph)
      ( λ x → Σ vertex-Directed-Graph (edge-Directed-Graph x))

  source-total-edge-Directed-Graph :
    total-edge-Directed-Graph → vertex-Directed-Graph
  source-total-edge-Directed-Graph = pr1

  target-total-edge-Directed-Graph :
    total-edge-Directed-Graph → vertex-Directed-Graph
  target-total-edge-Directed-Graph e = pr1 (pr2 e)

  edge-total-edge-Directed-Graph :
    (e : total-edge-Directed-Graph) →
    edge-Directed-Graph
      ( source-total-edge-Directed-Graph e)
      ( target-total-edge-Directed-Graph e)
  edge-total-edge-Directed-Graph e = pr2 (pr2 e)

  direct-predecessor-Directed-Graph :
    vertex-Directed-Graph → UU (l1 ⊔ l2)
  direct-predecessor-Directed-Graph x =
    Σ vertex-Directed-Graph (λ y → edge-Directed-Graph y x)

  direct-successor-Directed-Graph :
    vertex-Directed-Graph → UU (l1 ⊔ l2)
  direct-successor-Directed-Graph x =
    Σ vertex-Directed-Graph (edge-Directed-Graph x)
```

### Directed graphs (alternative definition)

```agda
module alternative where

  Directed-Graph' : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
  Directed-Graph' l1 l2 = Σ (UU l1) λ V → Σ (UU l2) (λ E → (E → V) × (E → V))

  module _
    {l1 l2 : Level} (G : Directed-Graph' l1 l2)
    where

    vertex-Directed-Graph' : UU l1
    vertex-Directed-Graph' = pr1 G

    edge-Directed-Graph' : UU l2
    edge-Directed-Graph' = pr1 (pr2 G)

    source-edge-Directed-Graph : edge-Directed-Graph' -> vertex-Directed-Graph'
    source-edge-Directed-Graph = pr1 (pr2 (pr2 G))

    target-edge-Directed-Graph : edge-Directed-Graph' -> vertex-Directed-Graph'
    target-edge-Directed-Graph = pr2 (pr2 (pr2 G))
```

## Properties

### The two definitions of directed graphs are equivalent

In the following code we construct functions back and forth. The fact that these
functions are mutual inverses remains to be formalized.

```agda
module equiv {l1 l2 : Level} where
  open alternative

  Directed-Graph-to-Directed-Graph' :
    Directed-Graph l1 l2 -> Directed-Graph' l1 (l1 ⊔ l2)
  pr1 (Directed-Graph-to-Directed-Graph' G) = vertex-Directed-Graph G
  pr1 (pr2 (Directed-Graph-to-Directed-Graph' G)) =
    Σ ( vertex-Directed-Graph G)
      ( λ x → Σ (vertex-Directed-Graph G) λ y → edge-Directed-Graph G x y)
  pr1 (pr2 (pr2 (Directed-Graph-to-Directed-Graph' G))) = pr1
  pr2 (pr2 (pr2 (Directed-Graph-to-Directed-Graph' G))) = pr1 ∘ pr2

  Directed-Graph'-to-Directed-Graph :
    Directed-Graph' l1 l2 -> Directed-Graph l1 (l1 ⊔ l2)
  pr1 (Directed-Graph'-to-Directed-Graph (V , E , st , tg)) = V
  pr2 (Directed-Graph'-to-Directed-Graph (V , E , st , tg)) x y =
    Σ E (λ e → (Id (st e) x) × (Id (tg e) y))
```

## External links

- [Digraph](https://ncatlab.org/nlab/show/digraph) at $n$Lab
- [Directed graph](https://ncatlab.org/nlab/show/directed+graph) at $n$Lab
- [Directed graph](https://www.wikidata.org/entity/Q1137726) on Wikidata
- [Directed graph](https://en.wikipedia.org/wiki/Directed_graph) at Wikipedia
- [Directed graph](https://mathworld.wolfram.com/DirectedGraph.html) at Wolfram
  Mathworld
