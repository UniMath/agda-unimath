# Eulerian circuits in undirected graphs

```agda
module graph-theory.eulerian-circuits-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.universe-levels

open import graph-theory.morphisms-undirected-graphs
open import graph-theory.polygons
open import graph-theory.undirected-graphs
```

</details>

## Idea

An
{{#concept "Eulerian circuit" Disambiguation="in an undirected graph" Agda=eulerian-circuit-Undirected-Graph}}
in an [undirected graph](graph-theory.undirected-graphs.md) `G` consists of a
[circuit](graph-theory.circuits-undirected-graphs.md) `T` in `G` such that every
edge in `G` is in the image of `T`. In other words, an Eulerian circuit `T`
consists of [`k`-gon](graph-theory.polygons.md) `H` equipped with a
[graph homomorphism](graph-theory.morphisms-undirected-graphs.md) `f : H → G`
that induces an [equivalence](foundation-core.equivalences.md)

```text
  Σ (unordered-pair-vertices-Polygon k H) (edge-Polygon k H) ≃
  Σ (unordered-pair-vertices-Undirected-Graph G) (edge-Undirected-Graph G)
```

## Definition

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  eulerian-circuit-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2)
  eulerian-circuit-Undirected-Graph =
    Σ ( ℕ)
      ( λ k →
        Σ ( Polygon k)
          ( λ H →
            Σ ( hom-Undirected-Graph (undirected-graph-Polygon k H) G)
              ( λ f →
                is-equiv
                  ( tot
                    ( edge-hom-Undirected-Graph
                      ( undirected-graph-Polygon k H)
                      ( G)
                      ( f))))))
```

## External links

- [Eulerian circuit](https://d3gt.com/unit.html?eulerian-circuit) on D3 Graph
  theory
- [Eulerian cycle](https://www.wikidata.org/entity/Q11691793) on Wikidata
- [Eulerian path](https://en.wikipedia.org/wiki/Eulerian_path) on Wikipedia
- [Eulerian cycle](https://mathworld.wolfram.com/EulerianCycle.html) on Wolfram
  mathworld
