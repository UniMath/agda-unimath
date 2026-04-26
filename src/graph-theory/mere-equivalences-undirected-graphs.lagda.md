# Mere equivalences of undirected graphs

```agda
module graph-theory.mere-equivalences-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import graph-theory.equivalences-undirected-graphs
open import graph-theory.undirected-graphs
```

</details>

## Idea

Two [undirected graphs](graph-theory.undirected-graphs.md) are said to be
{{#concept "merely equivalent" Disambiguation="undirected graphs" Agda=mere-equiv-Undirected-Graph}}
if there merely [exists](foundation.existential-quantification.md) an
[equivalence of undirected graphs](graph-theory.equivalences-undirected-graphs.md)
between them.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  where

  mere-equiv-Undirected-Graph-Prop : Prop (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  mere-equiv-Undirected-Graph-Prop = trunc-Prop (equiv-Undirected-Graph G H)

  mere-equiv-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  mere-equiv-Undirected-Graph = type-Prop mere-equiv-Undirected-Graph-Prop

  is-prop-mere-equiv-Undirected-Graph : is-prop mere-equiv-Undirected-Graph
  is-prop-mere-equiv-Undirected-Graph =
    is-prop-type-Prop mere-equiv-Undirected-Graph-Prop
```

## Properties

### The mere equivalence relation on undirected graphs is reflexive

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  refl-mere-equiv-Undirected-Graph : mere-equiv-Undirected-Graph G G
  refl-mere-equiv-Undirected-Graph =
    unit-trunc-Prop (id-equiv-Undirected-Graph G)
```

## External links

- [Graph isomoprhism](https://www.wikidata.org/entity/Q303100) at Wikidata
- [Graph isomorphism](https://en.wikipedia.org/wiki/Graph_isomorphism) at
  Wikipedia
- [Graph isomorphism](https://mathworld.wolfram.com/GraphIsomorphism.html) at
  Wolfram MathWorld
- [Isomorphism](https://ncatlab.org/nlab/show/isomorphism) at $n$Lab
