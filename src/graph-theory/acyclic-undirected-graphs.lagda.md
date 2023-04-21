# Acyclic undirected graphs

```agda
module graph-theory.acyclic-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import graph-theory.geometric-realizations-undirected-graphs
open import graph-theory.reflecting-maps-undirected-graphs
open import graph-theory.undirected-graphs
```

</details>

## Idea

An **acyclic** undirected graph is an undirected graph of which the geometric realization is contractible.

## Definition

### Acyclic undirected graphs

The following is a preliminary definition that requires us to parametrize over an extra universe level. This will not be necessary anymore if we constructed a geometric realization of every undirected graph. Once we did that, we would simply say that the geometric realization of `G` is contractible.

```agda
is-acyclic-Undirected-Graph :
  {l1 l2 : Level} (l : Level) (G : Undirected-Graph l1 l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
is-acyclic-Undirected-Graph l G =
  is-geometric-realization-reflecting-map-Undirected-Graph l G
    ( terminal-reflecting-map-Undirected-Graph G)
```
