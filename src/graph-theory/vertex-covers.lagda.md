# Vertex covers

```agda
module graph-theory.vertex-covers where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.undirected-graphs

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A vertex cover on a undirect graph is a set of vertices that includes at least
one extremity of each edge of the graph

## Definitions

```agda
vertex-cover :
  {l1 l2 : Level} → Undirected-Graph l1 l2 → UU (lsuc lzero ⊔ l1 ⊔ l2)
vertex-cover G =
  Σ ( vertex-Undirected-Graph G → Fin 2)
    ( λ c →
      (p : unordered-pair-vertices-Undirected-Graph G) →
      edge-Undirected-Graph G p →
        type-trunc-Prop
          ( Σ (vertex-Undirected-Graph G)
            ( λ x → is-in-unordered-pair p x × Id (c x) (inr star))))
```
