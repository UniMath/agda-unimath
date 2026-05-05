# Hypergraphs

```agda
module graph-theory.hypergraphs where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.unordered-tuples
```

</details>

## Idea

A `k`-{{#concept "hypergraph" WD="hypergraph" WDID=Q840247 Agda=Hypergraph}}
consists of a type `V` of vertices and a family `E` of types indexed by the
[unordered `k`-tuples](foundation.unordered-tuples.md) of vertices.

## Definition

```agda
Hypergraph : (l1 l2 : Level) (k : ℕ) → UU (lsuc l1 ⊔ lsuc l2)
Hypergraph l1 l2 k = Σ (UU l1) (λ V → unordered-tuple k V → UU l2)

module _
  {l1 l2 : Level} {k : ℕ} (G : Hypergraph l1 l2 k)
  where

  vertex-Hypergraph : UU l1
  vertex-Hypergraph = pr1 G

  unordered-tuple-vertices-Hypergraph : UU (lsuc lzero ⊔ l1)
  unordered-tuple-vertices-Hypergraph = unordered-tuple k vertex-Hypergraph

  simplex-Hypergraph : unordered-tuple-vertices-Hypergraph → UU l2
  simplex-Hypergraph = pr2 G
```

## External links

- [Hypergraph](https://ncatlab.org/nlab/show/hypergraph) at $n$Lab
- [Hypergraph](https://www.wikidata.org/entity/Q840247) on Wikidata
- [Hypergraph](https://en.wikipedia.org/wiki/Hypergraph) at Wikipedia
- [Hypergraph](https://mathworld.wolfram.com/Hypergraph.html) at Wolfram
  MathWorld
