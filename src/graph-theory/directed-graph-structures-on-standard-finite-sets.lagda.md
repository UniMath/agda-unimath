# Directed graph structures on standard finite sets

```agda
module graph-theory.directed-graph-structures-on-standard-finite-sets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A
{{#concept "directed graph structure" WD="directed graph" WDID=Q1137726 Agda=structure-directed-graph-Fin}}
on a [standard finite set](univalent-combinatorics.standard-finite-types.md)
`Fin n` is a [binary type-valued relation](foundation.binary-relations.md)

```text
  Fin n → Fin n → 𝒰.
```

## Definitions

### Directed graph structures on standard finite sets

```agda
structure-directed-graph-Fin : (l : Level) (n : ℕ) → UU (lsuc l)
structure-directed-graph-Fin l n = Fin n → Fin n → UU l
```

### Directed graphs on standard finite sets

```agda
Directed-Graph-Fin : (l : Level) → UU (lsuc l)
Directed-Graph-Fin l = Σ ℕ (structure-directed-graph-Fin l)
```

### Labeled finite directed graphs on standard finite sets

A
{{#concept "labeled finite directed graph" Agda=Labeled-Finite-Directed-Graph}}
consists of a [natural number](elementary-number-theory.natural-numbers.md) `n`
and a map `Fin n → Fin n → ℕ`.

```agda
Labeled-Finite-Directed-Graph : UU lzero
Labeled-Finite-Directed-Graph = Σ ℕ (λ n → Fin n → Fin n → ℕ)
```

## External links

- [Digraph](https://ncatlab.org/nlab/show/digraph) at $n$Lab
- [Directed graph](https://ncatlab.org/nlab/show/directed+graph) at $n$Lab
- [Directed graph](https://www.wikidata.org/entity/Q1137726) on Wikdiata
- [Directed graph](https://en.wikipedia.org/wiki/Directed_graph) at Wikipedia
- [Directed graph](https://mathworld.wolfram.com/DirectedGraph.html) at Wolfram
  MathWorld
