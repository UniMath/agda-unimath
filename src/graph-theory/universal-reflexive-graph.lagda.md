# The universal reflexive graph

```agda
open import foundation.function-extensionality-axiom

module
  graph-theory.universal-reflexive-graph
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import graph-theory.dependent-directed-graphs funext
open import graph-theory.dependent-reflexive-graphs funext
open import graph-theory.directed-graphs funext
open import graph-theory.reflexive-graphs funext
```

</details>

## Idea

The {{#concept "universal reflexive graph" Agda=universal-Reflexive-Graph}}
`𝒢 l` at [universe level](foundation.universe-levels.md) is a translation from
category theory into type theory of the Hofmann–Streicher universe
{{#cite Awodey22}} of presheaves on the reflexive graph category `Γʳ`

```text
      s
    ----->
  0 <-r--- 1,
    ----->
      t
```

in which we have `rs = id` and `rt = id`. The Hofmann–Streicher universe of
presheaves on a category `𝒞` is the presheaf

```text
     𝒰_𝒞 I := Presheaf 𝒞/I
  El_𝒞 I A := A 0,
```

where `0` is the terminal object of `𝒞/I`, i.e., the identity morphism on `I`.

We compute a few instances of the slice category `Γʳ/I`:

- The category Γʳ/0 is the category

  ```text
        s
      ----->
    1 <-r--- r
      ----->
        t
  ```

  in which we have `rs = id` and `rt = id`. In other words, we have an
  isomorphism of categories `Γʳ/0 ≅ Γʳ`.

- The category Γʳ/1 is the category

  ```text
         s                          s
       <-----                     ----->
    rs --r--> s -----> 1 <----- t <-r--- rt
       <-----                     ----->
         t                          t
  ```

  in which we have `rs = id` and `rt = id`.

This means that the universal reflexive graph `𝒰` can be defined type
theoretically as follows:

- The type of vertices of `𝒰` is the type of
  [reflexive graphs](graph-theory.reflexive-graphs.md).
- The type of edges from `G` to `H` is the type

  ```text
    G₀ → H₀ → Type
  ```

  of binary relations from the type `G₀` of vertices of `G` to the type `H₀` of
  vertices of `H`.

- The proof of reflexivity of a reflexive graph `G` is the relation

  ```text
    G₁ : G₀ → G₀ → Type
  ```

  of edges of `G`.

## Definitions

### The universal reflexive graph

```agda
module _
  (l1 l2 : Level)
  where

  vertex-universal-Reflexive-Graph : UU (lsuc l1 ⊔ lsuc l2)
  vertex-universal-Reflexive-Graph = Reflexive-Graph l1 l2

  edge-universal-Reflexvie-Graph :
    (G H : vertex-universal-Reflexive-Graph) → UU (l1 ⊔ lsuc l2)
  edge-universal-Reflexvie-Graph G H =
    vertex-Reflexive-Graph G → vertex-Reflexive-Graph H → UU l2

  refl-universal-Reflexive-Graph :
    (G : vertex-universal-Reflexive-Graph) →
    edge-universal-Reflexvie-Graph G G
  refl-universal-Reflexive-Graph G =
    edge-Reflexive-Graph G

  directed-graph-universal-Reflexive-Graph :
    Directed-Graph (lsuc l1 ⊔ lsuc l2) (l1 ⊔ lsuc l2)
  pr1 directed-graph-universal-Reflexive-Graph =
    vertex-universal-Reflexive-Graph
  pr2 directed-graph-universal-Reflexive-Graph =
    edge-universal-Reflexvie-Graph

  universal-Reflexive-Graph :
    Reflexive-Graph (lsuc l1 ⊔ lsuc l2) (l1 ⊔ lsuc l2)
  pr1 universal-Reflexive-Graph = directed-graph-universal-Reflexive-Graph
  pr2 universal-Reflexive-Graph = refl-universal-Reflexive-Graph
```

### The universal dependent directed graph

```agda
module _
  {l1 l2 : Level}
  where

  vertex-universal-Dependent-Reflexive-Graph :
    (G : vertex-universal-Reflexive-Graph l1 l2) → UU l1
  vertex-universal-Dependent-Reflexive-Graph G =
    vertex-Reflexive-Graph G

  edge-universal-Dependent-Reflexive-Graph :
    (G H : vertex-universal-Reflexive-Graph l1 l2)
    (R : edge-universal-Reflexvie-Graph l1 l2 G H) →
    vertex-universal-Dependent-Reflexive-Graph G →
    vertex-universal-Dependent-Reflexive-Graph H → UU l2
  edge-universal-Dependent-Reflexive-Graph G H R x y = R x y

  refl-universal-Dependent-Reflexive-Graph :
    (G : vertex-universal-Reflexive-Graph l1 l2)
    (x : vertex-universal-Dependent-Reflexive-Graph G) →
    edge-universal-Dependent-Reflexive-Graph G G
      ( refl-universal-Reflexive-Graph l1 l2 G) x x
  refl-universal-Dependent-Reflexive-Graph G x = refl-Reflexive-Graph G x

  dependent-directed-graph-universal-Dependent-Reflexive-Graph :
    Dependent-Directed-Graph l1 l2
      ( directed-graph-universal-Reflexive-Graph l1 l2)
  pr1 dependent-directed-graph-universal-Dependent-Reflexive-Graph =
    vertex-universal-Dependent-Reflexive-Graph
  pr2 dependent-directed-graph-universal-Dependent-Reflexive-Graph =
    edge-universal-Dependent-Reflexive-Graph

  universal-Dependent-Reflexive-Graph :
    Dependent-Reflexive-Graph l1 l2 (universal-Reflexive-Graph l1 l2)
  pr1 universal-Dependent-Reflexive-Graph =
    dependent-directed-graph-universal-Dependent-Reflexive-Graph
  pr2 universal-Dependent-Reflexive-Graph =
    refl-universal-Dependent-Reflexive-Graph
```

## Formalization target

There is a _reflexive graph duality theorem_, which asserts that for any
reflexive graph `G`, the type of morphisms `hom G 𝒰` from `G` into the universal
reflexive graph is equivalent to the type of pairs `(H , f)` consisting of a
reflexive graph `H` and a morphism `f : hom H G` from `H` into `G`. Such a
result should be formalized in a new file called `reflexive-graph-duality`.

## See also

- [The universal directed graph](graph-theory.universal-directed-graph.md)
