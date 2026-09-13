# Large reflexive graphs

```agda
module graph-theory.large-reflexive-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "large reflexive graph" Agda=Large-Reflexive-Graph}} is a large
directed graph [equipped](foundation.structure.md) with a loop edge at every
vertex.

## Definition

```agda
record
  Large-Reflexive-Graph
  (α : Level → Level) (β : Level → Level → Level) : UUω
  where

  field
    vertex-Large-Reflexive-Graph : (l : Level) → UU (α l)

    edge-Large-Reflexive-Graph :
      {l1 l2 : Level} →
      vertex-Large-Reflexive-Graph l1 →
      vertex-Large-Reflexive-Graph l2 → UU (β l1 l2)

    refl-Large-Reflexive-Graph :
      {l : Level} (x : vertex-Large-Reflexive-Graph l) →
      edge-Large-Reflexive-Graph x x

open Large-Reflexive-Graph public
```

## See also

- [Reflexive graphs](graph-theory.reflexive-graphs.md)

## External links

- [Reflexive graph](https://ncatlab.org/nlab/show/reflexive+graph) at $n$Lab
- [Graph](https://www.wikidata.org/entity/Q141488) on Wikidata
- [Directed graph](https://en.wikipedia.org/wiki/Directed_graph) at Wikipedia
- [Reflexive graph](https://mathworld.wolfram.com/ReflexiveGraph.html) at
  Wolfram MathWorld
