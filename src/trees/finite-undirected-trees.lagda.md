# Finite undirected trees

```agda
module trees.finite-undirected-trees where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.propositions
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.finite-undirected-graphs

open import trees.undirected-trees

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.pi-finite-types
open import univalent-combinatorics.symmetric-operations
```

</details>

## Idea

A **finite undirected tree** is a finite undirected graph such that between any two nodes there is a unique trail.

## Definitions

### The predicate of being a finite undirected tree

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph-𝔽 l1 l2)
  where

  is-tree-Undirected-Graph-𝔽-Prop : Prop (lsuc lzero ⊔ l1 ⊔ l2)
  is-tree-Undirected-Graph-𝔽-Prop =
    is-tree-Undirected-Graph-Prop
      ( undirected-graph-Undirected-Graph-𝔽 G)

  is-tree-Undirected-Graph-𝔽 : UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-tree-Undirected-Graph-𝔽 =
    type-Prop is-tree-Undirected-Graph-𝔽-Prop
```

### The type of finite undirected trees

```agda
Undirected-Tree-𝔽 : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Undirected-Tree-𝔽 l1 l2 = Σ (Undirected-Graph-𝔽 l1 l2) is-tree-Undirected-Graph-𝔽
```

### Finite trees of cardinality `n`

```agda
Undirected-Tree-Of-Size :
  (l1 l2 : Level) (n : ℕ) → UU (lsuc l1)
Undirected-Tree-Of-Size l1 l2 n =
  Σ ( UU-Fin l1 n)
    ( λ V →
      Σ ( unordered-pair (type-UU-Fin n V) → Decidable-Prop lzero)
        ( λ E →
          is-tree-Undirected-Graph
            ( type-UU-Fin n V , λ p → type-Decidable-Prop (E p))))

module _
  {l1 l2 : Level} (n : ℕ) (T : Undirected-Tree-Of-Size l1 l2 n)
  where

  node-Undirected-Tree-Of-Size : UU l1
  node-Undirected-Tree-Of-Size = type-UU-Fin n (pr1 T)

  has-cardinality-node-Undirected-Tree-Of-Size :
    has-cardinality n node-Undirected-Tree-Of-Size
  has-cardinality-node-Undirected-Tree-Of-Size =
    has-cardinality-type-UU-Fin n (pr1 T)

  is-finite-node-Undirected-Tree-Of-Size :
    is-finite node-Undirected-Tree-Of-Size
  is-finite-node-Undirected-Tree-Of-Size =
    is-finite-has-cardinality n has-cardinality-node-Undirected-Tree-Of-Size

  node-finite-type-Undirected-Tree-Of-Size : 𝔽 l1
  pr1 node-finite-type-Undirected-Tree-Of-Size =
    node-Undirected-Tree-Of-Size
  pr2 node-finite-type-Undirected-Tree-Of-Size =
    is-finite-node-Undirected-Tree-Of-Size

  unordered-pair-nodes-Undirected-Tree-Of-Size : UU (lsuc lzero ⊔ l1)
  unordered-pair-nodes-Undirected-Tree-Of-Size =
    unordered-pair node-Undirected-Tree-Of-Size

  edge-decidable-prop-Undirected-Tree-Of-Size :
    unordered-pair-nodes-Undirected-Tree-Of-Size → Decidable-Prop lzero
  edge-decidable-prop-Undirected-Tree-Of-Size = pr1 (pr2 T)

  edge-Undirected-Tree-Of-Size :
    unordered-pair-nodes-Undirected-Tree-Of-Size → UU lzero
  edge-Undirected-Tree-Of-Size =
    type-Decidable-Prop ∘ edge-decidable-prop-Undirected-Tree-Of-Size

  is-decidable-prop-edge-Undirected-Tree-Of-Size :
    (p : unordered-pair-nodes-Undirected-Tree-Of-Size) →
    is-decidable-prop (edge-Undirected-Tree-Of-Size p)
  is-decidable-prop-edge-Undirected-Tree-Of-Size p =
    is-decidable-prop-type-Decidable-Prop
      ( edge-decidable-prop-Undirected-Tree-Of-Size p)

  is-finite-edge-Undirected-Tree-Of-Size :
    (p : unordered-pair-nodes-Undirected-Tree-Of-Size) →
    is-finite (edge-Undirected-Tree-Of-Size p)
  is-finite-edge-Undirected-Tree-Of-Size p =
    is-finite-type-Decidable-Prop ?
```

## Properties

### The type of finite undirected trees of cardinality `n` is π-finite

```agda
is-π-finite-Undirected-Tree-of-cardinality :
  (k n : ℕ) → is-π-finite k (Undirected-Tree-Of-Size lzero lzero n)
is-π-finite-Undirected-Tree-of-cardinality k n =
  is-π-finite-Σ k
    ( is-π-finite-UU-Fin (succ-ℕ k) n)
    ( λ (X , H) →
      is-π-finite-Σ k
        ( is-π-finite-is-finite
          ( succ-ℕ k)
          ( is-finite-symmetric-operation
            ( is-finite-has-cardinality n H)
            ( is-finite-Decidable-Prop)))
        ( λ E →
          {!!}))
```
