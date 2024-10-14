# The universal directed graph

```agda
module graph-theory.universal-directed-graph where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import graph-theory.dependent-directed-graphs
open import graph-theory.directed-graphs
```

</details>

## Idea

The {{#concpept "universal directed graph"}} `𝒢 l` at
[universe level](foundation.universe-levels.md) `l` has the universe `UU l` as
its type of vertices, and spans between types as its edges.

Specifically, the universal directed graph is a translation from category theory
into type theory of the Hofmann-Streicher universe {{#cite Awodey22}} of
presheaves on the representing pair of arrows

```text
      s
    ----->
  0 -----> 1
      t
```

The Hofmann-Streicher universe of presheaves on a category `𝒞` is the presheaf

```text
     𝒰_𝒞 I := Presheaf 𝒞/I
  El_𝒞 I A := A *,
```

where `*` is the terminal object of `𝒞/I`, i.e., the identity morphism on `I`.

We compute a the instances of the slice category `⇉/I`:

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
  pr2 universal-Dependent-Directed-Graph =
    edge-universal-Dependent-Directed-Graph
    
```

## Formalization target

There is a _directed graph duality theorem_, which asserts that for any directed
graph `G`, the type of morphisms `hom G 𝒰` from `G` into the universal directed
graph is equivalent to the type of pairs `(H , f)` consisting of a directed
graph `H` and a morphism `f : hom H G` from `H` into `G`. Such a result should
be formalized in a new file called `directed-graph-duality`.

## See also

- [The universal reflexive graph](graph-theory.universal-reflexive-graph.md)
