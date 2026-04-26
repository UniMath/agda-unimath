# Geometric realizations of undirected graphs

```agda
module graph-theory.geometric-realizations-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.symmetric-identity-types
open import foundation.universe-levels

open import graph-theory.reflecting-maps-undirected-graphs
open import graph-theory.undirected-graphs
```

</details>

## Idea

The {{#concept "geometric realization" Disambiguation="of an undirected graph"}}
of an [undirected graph](graph-theory.undirected-graphs.md) `G` is the initial
type `X` equipped with a
[reflecting map](graph-theory.reflecting-maps-undirected-graphs.md) from `G`
into `X`.

## Definition

```agda
precomp-reflecting-map-Undirected-Graph :
  {l1 l2 l3 l4 : Level} (G : Undirected-Graph l1 l2) {X : UU l3} (Y : UU l4) →
  reflecting-map-Undirected-Graph G X →
  (X → Y) → reflecting-map-Undirected-Graph G Y
pr1 (precomp-reflecting-map-Undirected-Graph G Y f h) =
  h ∘ vertex-reflecting-map-Undirected-Graph G f
pr2 (precomp-reflecting-map-Undirected-Graph G Y f h) v e =
  map-symmetric-Id h
    ( unordered-pair-vertices-reflecting-map-Undirected-Graph G f v)
    ( edge-reflecting-map-Undirected-Graph G f v e)

is-geometric-realization-reflecting-map-Undirected-Graph :
  {l1 l2 l3 : Level} (l : Level) (G : Undirected-Graph l1 l2) {X : UU l3}
  (f : reflecting-map-Undirected-Graph G X) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l)
is-geometric-realization-reflecting-map-Undirected-Graph l G f =
  (Y : UU l) → is-equiv (precomp-reflecting-map-Undirected-Graph G Y f)
```

## External links

- [Geometric realization](https://ncatlab.org/nlab/show/geometric+realization)
  at $n$Lab
