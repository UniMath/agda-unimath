# The universal directed graph

```agda
module graph-theory.universal-directed-graph where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import graph-theory.base-change-dependent-directed-graphs
open import graph-theory.dependent-directed-graphs
open import graph-theory.directed-graphs
open import graph-theory.equivalences-dependent-directed-graphs
open import graph-theory.morphisms-directed-graphs
```

</details>

## Idea

The {{#concpept "universal directed graph" Agda=universal-Directed-Graph}} `𝒢 l`
at [universe level](foundation.universe-levels.md) `l` is the
[directed graph](graph-theory.directed-graphs.md) that has the universe `UU l`
as its type of vertices, and spans between types as its edges.

Specifically, the universal directed graph is a translation from category theory
into type theory of the Hofmann–Streicher universe {{#cite Awodey22}} of
presheaves on the representing pair of arrows

```text
      s
    ----->
  0 -----> 1
      t
```

The Hofmann–Streicher universe of presheaves on a category `𝒞` is the presheaf

```text
     𝒰_𝒞 I := Presheaf 𝒞/I
  El_𝒞 I A := A *,
```

where `*` is the terminal object of `𝒞/I`, i.e., the identity morphism on `I`.

We compute the instances of the slice category `⇉/I`:

- The slice category `⇉/0` is the terminal category.
- The slice category `⇉/1` is the representing cospan

  ```text
        s         t
    s -----> 1 <----- t
  ```

  The functors `s t : ⇉/0 → ⇉/1` are given by `* ↦ s` and `* ↦ t`, respectively.

This means that:

- The type of vertices of the universal directed graph is the universe of types
  `UU l`.
- The type of edges from `X` to `Y` of the universal directed graph is the type
  of spans from `X` to `Y`.

There is a
[directed graph duality theorem](graph-theory.directed-graph-duality.md), which
asserts that for any directed graph `G`, the type of
[morphisms](graph-theory.morphisms-directed-graphs.md) `hom G 𝒰` from `G` into
the universal directed graph is [equivalent](foundation-core.equivalences.md) to
the type of pairs `(H , f)` consisting of a directed graph `H` and a morphism
`f : hom H G` from `H` into `G`.

## Definitions

### The universal directed graph

```agda
module _
  (l1 l2 : Level)
  where

  vertex-universal-Directed-Graph : UU (lsuc l1)
  vertex-universal-Directed-Graph = UU l1

  edge-universal-Directed-Graph :
    (X Y : vertex-universal-Directed-Graph) → UU (l1 ⊔ lsuc l2)
  edge-universal-Directed-Graph X Y = X → Y → UU l2

  universal-Directed-Graph : Directed-Graph (lsuc l1) (l1 ⊔ lsuc l2)
  pr1 universal-Directed-Graph = vertex-universal-Directed-Graph
  pr2 universal-Directed-Graph = edge-universal-Directed-Graph
```

### The universal dependent directed graph

```agda
module _
  (l1 l2 : Level)
  where

  vertex-universal-Dependent-Directed-Graph :
    vertex-universal-Directed-Graph l1 l2 → UU l1
  vertex-universal-Dependent-Directed-Graph X = X

  edge-universal-Dependent-Directed-Graph :
    {X Y : vertex-universal-Directed-Graph l1 l2}
    (R : edge-universal-Directed-Graph l1 l2 X Y) →
    vertex-universal-Dependent-Directed-Graph X →
    vertex-universal-Dependent-Directed-Graph Y → UU l2
  edge-universal-Dependent-Directed-Graph R x y = R x y

  universal-Dependent-Directed-Graph :
    Dependent-Directed-Graph l1 l2 (universal-Directed-Graph l1 l2)
  pr1 universal-Dependent-Directed-Graph =
    vertex-universal-Dependent-Directed-Graph
  pr2 universal-Dependent-Directed-Graph _ _ =
    edge-universal-Dependent-Directed-Graph
```

## Properties

### Every dependent directed graph is a base change of the universal dependent directed graph

#### The characteristic morphism of a dependent directed graph

```agda
module _
  {l1 l2 l3 l4 : Level}
  {G : Directed-Graph l1 l2} (H : Dependent-Directed-Graph l3 l4 G)
  where

  vertex-characteristic-hom-Dependent-Directed-Graph :
    vertex-Directed-Graph G → UU l3
  vertex-characteristic-hom-Dependent-Directed-Graph =
    vertex-Dependent-Directed-Graph H

  edge-characteristic-hom-Dependent-Directed-Graph :
    {x y : vertex-Directed-Graph G} (e : edge-Directed-Graph G x y) →
    vertex-characteristic-hom-Dependent-Directed-Graph x →
    vertex-characteristic-hom-Dependent-Directed-Graph y →
    UU l4
  edge-characteristic-hom-Dependent-Directed-Graph =
    edge-Dependent-Directed-Graph H

  characteristic-hom-Dependent-Directed-Graph :
    hom-Directed-Graph G (universal-Directed-Graph l3 l4)
  pr1 characteristic-hom-Dependent-Directed-Graph =
    vertex-characteristic-hom-Dependent-Directed-Graph
  pr2 characteristic-hom-Dependent-Directed-Graph _ _ =
    edge-characteristic-hom-Dependent-Directed-Graph
```

#### Base change of the universal dependent directed graph along the characteristic morphism of a dependent directed graph

```agda
module _
  {l1 l2 l3 l4 : Level}
  {G : Directed-Graph l1 l2} (H : Dependent-Directed-Graph l3 l4 G)
  where

  base-change-universal-graph-characteristic-hom-Dependent-Directed-Graph :
    Dependent-Directed-Graph l3 l4 G
  base-change-universal-graph-characteristic-hom-Dependent-Directed-Graph =
    base-change-Dependent-Directed-Graph G
      ( characteristic-hom-Dependent-Directed-Graph H)
      ( universal-Dependent-Directed-Graph l3 l4)

  compute-base-change-universal-graph-characteristic-hom-Dependent-Directed-Graph :
    equiv-Dependent-Directed-Graph H
      base-change-universal-graph-characteristic-hom-Dependent-Directed-Graph
  compute-base-change-universal-graph-characteristic-hom-Dependent-Directed-Graph =
    id-equiv-Dependent-Directed-Graph H
```

## See also

- [The universal reflexive graph](graph-theory.universal-reflexive-graph.md)
- [Directed graph duality](graph-theory.directed-graph-duality.md)
