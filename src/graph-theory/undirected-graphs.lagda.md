# Undirected graphs

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module graph-theory.undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.symmetric-binary-relations
open import foundation.transport
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.directed-graphs
```

</details>

## Idea

An **undirected graph** consists of a type `V` of **vertices** and a
[symmetric binary relation](foundation.symmetric-binary-relations.md) `E` edges.

Note that in `agda-unimath`, symmetric binary relations on a type `V` are
families of types over the [unordered pairs](foundation.unordered-pairs.md) of
`V`. In other words, the edge relation of an undirected graph is assumed to be
fully coherently symmetric. Furthermore, there may be multiple edges between
vertices in an undirected graph, and undirected graphs may contain loops, i.e.,
edges from a vertex to itself.

## Definitions

### Undirected graphs

```agda
Undirected-Graph : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Undirected-Graph l1 l2 = Σ (UU l1) (symmetric-binary-relation l2)

module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  vertex-Undirected-Graph : UU l1
  vertex-Undirected-Graph = pr1 G

  unordered-pair-vertices-Undirected-Graph : UU (lsuc lzero ⊔ l1)
  unordered-pair-vertices-Undirected-Graph =
    unordered-pair vertex-Undirected-Graph

  type-unordered-pair-vertices-Undirected-Graph :
    unordered-pair-vertices-Undirected-Graph → UU lzero
  type-unordered-pair-vertices-Undirected-Graph p = type-unordered-pair p

  element-unordered-pair-vertices-Undirected-Graph :
    (p : unordered-pair-vertices-Undirected-Graph) →
    type-unordered-pair-vertices-Undirected-Graph p → vertex-Undirected-Graph
  element-unordered-pair-vertices-Undirected-Graph p = element-unordered-pair p

  edge-Undirected-Graph : symmetric-binary-relation l2 vertex-Undirected-Graph
  edge-Undirected-Graph = pr2 G

  total-edge-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2)
  total-edge-Undirected-Graph =
    Σ unordered-pair-vertices-Undirected-Graph edge-Undirected-Graph

  abstract
    equiv-tr-edge-Undirected-Graph :
      (p q : unordered-pair-vertices-Undirected-Graph) →
      Eq-unordered-pair p q → edge-Undirected-Graph p ≃ edge-Undirected-Graph q
    equiv-tr-edge-Undirected-Graph =
      equiv-tr-symmetric-binary-relation edge-Undirected-Graph

    compute-refl-equiv-tr-edge-Undirected-Graph :
      (p : unordered-pair-vertices-Undirected-Graph) →
      equiv-tr-edge-Undirected-Graph p p (refl-Eq-unordered-pair p) ＝ id-equiv
    compute-refl-equiv-tr-edge-Undirected-Graph =
      compute-refl-equiv-tr-symmetric-binary-relation edge-Undirected-Graph

    htpy-compute-refl-equiv-tr-edge-Undirected-Graph :
      (p : unordered-pair-vertices-Undirected-Graph) →
      htpy-equiv
        ( equiv-tr-edge-Undirected-Graph p p (refl-Eq-unordered-pair p))
        ( id-equiv)
    htpy-compute-refl-equiv-tr-edge-Undirected-Graph =
      htpy-compute-refl-equiv-tr-symmetric-binary-relation edge-Undirected-Graph

  abstract
    tr-edge-Undirected-Graph :
      (p q : unordered-pair-vertices-Undirected-Graph) →
      Eq-unordered-pair p q → edge-Undirected-Graph p → edge-Undirected-Graph q
    tr-edge-Undirected-Graph =
      tr-symmetric-binary-relation edge-Undirected-Graph

    compute-refl-tr-edge-Undirected-Graph :
      (p : unordered-pair-vertices-Undirected-Graph) →
      tr-edge-Undirected-Graph p p (refl-Eq-unordered-pair p) ＝ id
    compute-refl-tr-edge-Undirected-Graph =
      compute-refl-tr-symmetric-binary-relation edge-Undirected-Graph

    htpy-compute-refl-tr-edge-Undirected-Graph :
      (p : unordered-pair-vertices-Undirected-Graph) →
      tr-edge-Undirected-Graph p p (refl-Eq-unordered-pair p) ~ id
    htpy-compute-refl-tr-edge-Undirected-Graph =
      htpy-compute-refl-tr-symmetric-binary-relation edge-Undirected-Graph
```
