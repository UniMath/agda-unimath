# Walks in finite undirected graphs

```agda
module graph-theory.walks-finite-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.finite-undirected-graphs
open import graph-theory.walks-undirected-graphs

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A **walk** in a
[finite undirected graph](graph-theory.finite-undirected-graphs.md) `G` is
simply a [walk](graph-theory.walks-undirected-graphs.md) in its underlying
[undirected graph](graph-theory.undirected-graphs.md).

Note that the type of walks in a finite undirected graph does not need to be
[finite](univalent-combinatorics.finite-types.md), since edges can be repeated
in walks. However, the type of walks from `x` to `y` in a finite undirected
graph has [decidable equality](foundation.decidable-equality.md), and the type
of walks of a given length `n` in a finite undirected graph is finite.

## Definition

### Walks in finite undirected graphs

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph-𝔽 l1 l2)
  where

  walk-Undirected-Graph-𝔽 :
    (x y : vertex-Undirected-Graph-𝔽 G) → UU (lsuc lzero ⊔ l1 ⊔ l2)
  walk-Undirected-Graph-𝔽 =
    walk-Undirected-Graph (undirected-graph-Undirected-Graph-𝔽 G)
```

### The vertices on a walk in a finite undirected graph

```agda
module _
  {l1 l2 : Level}
  (G : Undirected-Graph-𝔽 l1 l2) {x : vertex-Undirected-Graph-𝔽 G}
  where

  is-vertex-on-walk-Undirected-Graph-𝔽 :
    {y : vertex-Undirected-Graph-𝔽 G} (w : walk-Undirected-Graph-𝔽 G x y) →
    vertex-Undirected-Graph-𝔽 G → UU l1
  is-vertex-on-walk-Undirected-Graph-𝔽 =
    is-vertex-on-walk-Undirected-Graph (undirected-graph-Undirected-Graph-𝔽 G)

  vertex-on-walk-Undirected-Graph-𝔽 :
    {y : vertex-Undirected-Graph-𝔽 G}
    (w : walk-Undirected-Graph-𝔽 G x y) → UU l1
  vertex-on-walk-Undirected-Graph-𝔽 =
    vertex-on-walk-Undirected-Graph (undirected-graph-Undirected-Graph-𝔽 G)

  vertex-vertex-on-walk-Undirected-Graph-𝔽 :
    {y : vertex-Undirected-Graph-𝔽 G} (w : walk-Undirected-Graph-𝔽 G x y) →
    vertex-on-walk-Undirected-Graph-𝔽 w → vertex-Undirected-Graph-𝔽 G
  vertex-vertex-on-walk-Undirected-Graph-𝔽 =
    vertex-vertex-on-walk-Undirected-Graph
      ( undirected-graph-Undirected-Graph-𝔽 G)
```

### Edges on a walk

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph-𝔽 l1 l2)
  {x : vertex-Undirected-Graph-𝔽 G}
  where

  is-edge-on-walk-Undirected-Graph-𝔽' :
    {y : vertex-Undirected-Graph-𝔽 G} (w : walk-Undirected-Graph-𝔽 G x y) →
    total-edge-Undirected-Graph-𝔽 G → UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-edge-on-walk-Undirected-Graph-𝔽' =
    is-edge-on-walk-Undirected-Graph' (undirected-graph-Undirected-Graph-𝔽 G)

  is-edge-on-walk-Undirected-Graph-𝔽 :
    {y : vertex-Undirected-Graph-𝔽 G} (w : walk-Undirected-Graph-𝔽 G x y) →
    (p : unordered-pair-vertices-Undirected-Graph-𝔽 G) →
    edge-Undirected-Graph-𝔽 G p → UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-edge-on-walk-Undirected-Graph-𝔽 =
    is-edge-on-walk-Undirected-Graph (undirected-graph-Undirected-Graph-𝔽 G)

  edge-on-walk-Undirected-Graph-𝔽 :
    {y : vertex-Undirected-Graph-𝔽 G} (w : walk-Undirected-Graph-𝔽 G x y) →
    UU (lsuc lzero ⊔ l1 ⊔ l2)
  edge-on-walk-Undirected-Graph-𝔽 =
    edge-on-walk-Undirected-Graph (undirected-graph-Undirected-Graph-𝔽 G)

  edge-edge-on-walk-Undirected-Graph-𝔽 :
    {y : vertex-Undirected-Graph-𝔽 G}
    (w : walk-Undirected-Graph-𝔽 G x y) →
    edge-on-walk-Undirected-Graph-𝔽 w → total-edge-Undirected-Graph-𝔽 G
  edge-edge-on-walk-Undirected-Graph-𝔽 =
    edge-edge-on-walk-Undirected-Graph (undirected-graph-Undirected-Graph-𝔽 G)
```

### Concatenating walks

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph-𝔽 l1 l2)
  {x : vertex-Undirected-Graph-𝔽 G}
  where

  concat-walk-Undirected-Graph-𝔽 :
    {y z : vertex-Undirected-Graph-𝔽 G} →
    walk-Undirected-Graph-𝔽 G x y →
    walk-Undirected-Graph-𝔽 G y z →
    walk-Undirected-Graph-𝔽 G x z
  concat-walk-Undirected-Graph-𝔽 =
    concat-walk-Undirected-Graph (undirected-graph-Undirected-Graph-𝔽 G)
```

### The length of a walk

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph-𝔽 l1 l2)
  {x : vertex-Undirected-Graph-𝔽 G}
  where

  length-walk-Undirected-Graph-𝔽 :
    {y : vertex-Undirected-Graph-𝔽 G} → walk-Undirected-Graph-𝔽 G x y → ℕ
  length-walk-Undirected-Graph-𝔽 =
    length-walk-Undirected-Graph (undirected-graph-Undirected-Graph-𝔽 G)
```

### Walks of a fixed length

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph-𝔽 l1 l2)
  (x : vertex-Undirected-Graph-𝔽 G)
  where

  walk-of-length-Undirected-Graph-𝔽 :
    ℕ → vertex-Undirected-Graph-𝔽 G → UU (lsuc lzero ⊔ l1 ⊔ l2)
  walk-of-length-Undirected-Graph-𝔽 =
    walk-of-length-Undirected-Graph (undirected-graph-Undirected-Graph-𝔽 G) x

  map-compute-total-walk-of-length-Undirected-Graph-𝔽 :
    (y : vertex-Undirected-Graph-𝔽 G) →
    walk-Undirected-Graph-𝔽 G x y →
    Σ ℕ (λ n → walk-of-length-Undirected-Graph-𝔽 n y)
  map-compute-total-walk-of-length-Undirected-Graph-𝔽 =
    map-compute-total-walk-of-length-Undirected-Graph
      ( undirected-graph-Undirected-Graph-𝔽 G)
      ( x)

  map-inv-compute-total-walk-of-length-Undirected-Graph-𝔽 :
    (y : vertex-Undirected-Graph-𝔽 G) →
    Σ ℕ (λ n → walk-of-length-Undirected-Graph-𝔽 n y) →
    walk-Undirected-Graph-𝔽 G x y
  map-inv-compute-total-walk-of-length-Undirected-Graph-𝔽 =
    map-inv-compute-total-walk-of-length-Undirected-Graph
      ( undirected-graph-Undirected-Graph-𝔽 G)
      ( x)

  issec-map-inv-compute-total-walk-of-length-Undirected-Graph-𝔽 :
    (y : vertex-Undirected-Graph-𝔽 G) →
    ( map-compute-total-walk-of-length-Undirected-Graph-𝔽 y ∘
      map-inv-compute-total-walk-of-length-Undirected-Graph-𝔽 y) ~ id
  issec-map-inv-compute-total-walk-of-length-Undirected-Graph-𝔽 =
    issec-map-inv-compute-total-walk-of-length-Undirected-Graph
      ( undirected-graph-Undirected-Graph-𝔽 G)
      ( x)

  isretr-map-inv-compute-total-walk-of-length-Undirected-Graph-𝔽 :
    (y : vertex-Undirected-Graph-𝔽 G) →
    ( map-inv-compute-total-walk-of-length-Undirected-Graph-𝔽 y ∘
      map-compute-total-walk-of-length-Undirected-Graph-𝔽 y) ~ id
  isretr-map-inv-compute-total-walk-of-length-Undirected-Graph-𝔽 =
    isretr-map-inv-compute-total-walk-of-length-Undirected-Graph
      ( undirected-graph-Undirected-Graph-𝔽 G)
      ( x)

  is-equiv-map-compute-total-walk-of-length-Undirected-Graph-𝔽 :
    (y : vertex-Undirected-Graph-𝔽 G) →
    is-equiv (map-compute-total-walk-of-length-Undirected-Graph-𝔽 y)
  is-equiv-map-compute-total-walk-of-length-Undirected-Graph-𝔽 =
    is-equiv-map-compute-total-walk-of-length-Undirected-Graph
      ( undirected-graph-Undirected-Graph-𝔽 G)
      ( x)

  compute-total-walk-of-length-Undirected-Graph-𝔽 :
    (y : vertex-Undirected-Graph-𝔽 G) →
    walk-Undirected-Graph-𝔽 G x y ≃
    Σ ℕ (λ n → walk-of-length-Undirected-Graph-𝔽 n y)
  compute-total-walk-of-length-Undirected-Graph-𝔽 =
    compute-total-walk-of-length-Undirected-Graph
      ( undirected-graph-Undirected-Graph-𝔽 G)
      ( x)
```

## Properties

### The type of vertices on the constant walk is contractible

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph-𝔽 l1 l2)
  (x : vertex-Undirected-Graph-𝔽 G)
  where

  is-contr-vertex-on-walk-refl-walk-Undirected-Graph-𝔽 :
    is-contr
      ( vertex-on-walk-Undirected-Graph-𝔽 G
        ( refl-walk-Undirected-Graph {x = x}))
  is-contr-vertex-on-walk-refl-walk-Undirected-Graph-𝔽 =
    is-contr-vertex-on-walk-refl-walk-Undirected-Graph
      ( undirected-graph-Undirected-Graph-𝔽 G)
      ( x)
```

### The type of vertices on a walk is equivalent to `Fin (n + 1)` where `n` is the length of the walk

```agda
module _
  {l1 l2 : Level}
  (G : Undirected-Graph-𝔽 l1 l2)
  {x : vertex-Undirected-Graph-𝔽 G}
  where

  compute-vertex-on-walk-Undirected-Graph-𝔽 :
    {y : vertex-Undirected-Graph-𝔽 G} (w : walk-Undirected-Graph-𝔽 G x y) →
    vertex-on-walk-Undirected-Graph-𝔽 G w ≃
    Fin (succ-ℕ (length-walk-Undirected-Graph-𝔽 G w))
  compute-vertex-on-walk-Undirected-Graph-𝔽 =
    compute-vertex-on-walk-Undirected-Graph
      ( undirected-graph-Undirected-Graph-𝔽 G)
```

### The type of edges on a constant walk is empty

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph-𝔽 l1 l2)
  (x : vertex-Undirected-Graph-𝔽 G)
  where

  is-empty-edge-on-walk-refl-walk-Undirected-Graph-𝔽 :
    is-empty
      ( edge-on-walk-Undirected-Graph-𝔽 G
        ( refl-walk-Undirected-Graph {x = x}))
  is-empty-edge-on-walk-refl-walk-Undirected-Graph-𝔽 =
    is-empty-edge-on-walk-refl-walk-Undirected-Graph
      ( undirected-graph-Undirected-Graph-𝔽 G)
      ( x)
```

### The type of edges on a walk is equivalent to `Fin n` where `n` is the length of the walk

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph-𝔽 l1 l2)
  {x : vertex-Undirected-Graph-𝔽 G}
  where

  compute-edge-on-walk-Undirected-Graph-𝔽 :
    {y : vertex-Undirected-Graph-𝔽 G}
    (w : walk-Undirected-Graph-𝔽 G x y) →
    edge-on-walk-Undirected-Graph-𝔽 G w ≃
    Fin (length-walk-Undirected-Graph-𝔽 G w)
  compute-edge-on-walk-Undirected-Graph-𝔽 =
    compute-edge-on-walk-Undirected-Graph
      ( undirected-graph-Undirected-Graph-𝔽 G)
```

### Right unit law for concatenation of walks

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph-𝔽 l1 l2)
  {x : vertex-Undirected-Graph-𝔽 G}
  where

  right-unit-law-concat-walk-Undirected-Graph-𝔽 :
    {y : vertex-Undirected-Graph-𝔽 G}
    (w : walk-Undirected-Graph-𝔽 G x y) →
    (concat-walk-Undirected-Graph-𝔽 G w refl-walk-Undirected-Graph) ＝ w
  right-unit-law-concat-walk-Undirected-Graph-𝔽 =
    right-unit-law-concat-walk-Undirected-Graph
      ( undirected-graph-Undirected-Graph-𝔽 G)
```

### For any walk `w` from `x` to `y` and any vertex `v` on `w`, we can decompose `w` into a walk `w1` from `x` to `v` and a walk `w2` from `v` to `y`

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph-𝔽 l1 l2)
  {x : vertex-Undirected-Graph-𝔽 G}
  where

  first-segment-walk-Undirected-Graph-𝔽 :
    {y : vertex-Undirected-Graph-𝔽 G} (w : walk-Undirected-Graph-𝔽 G x y)
    (v : vertex-on-walk-Undirected-Graph-𝔽 G w) →
    walk-Undirected-Graph-𝔽 G x (vertex-vertex-on-walk-Undirected-Graph-𝔽 G w v)
  first-segment-walk-Undirected-Graph-𝔽 =
    first-segment-walk-Undirected-Graph (undirected-graph-Undirected-Graph-𝔽 G)

  second-segment-walk-Undirected-Graph-𝔽 :
    {y : vertex-Undirected-Graph-𝔽 G} (w : walk-Undirected-Graph-𝔽 G x y)
    (v : vertex-on-walk-Undirected-Graph-𝔽 G w) →
    walk-Undirected-Graph-𝔽 G (vertex-vertex-on-walk-Undirected-Graph-𝔽 G w v) y
  second-segment-walk-Undirected-Graph-𝔽 =
    second-segment-walk-Undirected-Graph (undirected-graph-Undirected-Graph-𝔽 G)

  eq-decompose-walk-Undirected-Graph-𝔽 :
    {y : vertex-Undirected-Graph-𝔽 G} (w : walk-Undirected-Graph-𝔽 G x y)
    (v : vertex-on-walk-Undirected-Graph-𝔽 G w) →
    ( concat-walk-Undirected-Graph-𝔽 G
      ( first-segment-walk-Undirected-Graph-𝔽 w v)
      ( second-segment-walk-Undirected-Graph-𝔽 w v)) ＝ w
  eq-decompose-walk-Undirected-Graph-𝔽 =
    eq-decompose-walk-Undirected-Graph (undirected-graph-Undirected-Graph-𝔽 G)
```

### For any edge `e` on `p`, if `v` is a vertex on `w` then it is a vertex on `cons p e w`

```agda
is-vertex-on-walk-cons-walk-Undirected-Graph-𝔽 :
  {l1 l2 : Level} (G : Undirected-Graph-𝔽 l1 l2)
  (p : unordered-pair-vertices-Undirected-Graph-𝔽 G)
  (e : edge-Undirected-Graph-𝔽 G p) →
  {x : vertex-Undirected-Graph-𝔽 G} {y : type-unordered-pair p} →
  (w : walk-Undirected-Graph-𝔽 G x (element-unordered-pair p y)) →
  {v : vertex-Undirected-Graph-𝔽 G} →
  is-vertex-on-walk-Undirected-Graph-𝔽 G w v →
  is-vertex-on-walk-Undirected-Graph-𝔽 G (cons-walk-Undirected-Graph p e w) v
is-vertex-on-walk-cons-walk-Undirected-Graph-𝔽 G =
  is-vertex-on-walk-cons-walk-Undirected-Graph
    ( undirected-graph-Undirected-Graph-𝔽 G)
```

### For any decomposition of a walk `w` into `w1` followed by `w2`, any vertex on `w` is a vertex on `w1` or on `w2`

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph-𝔽 l1 l2)
  {x : vertex-Undirected-Graph-𝔽 G}
  where

  is-vertex-on-first-segment-walk-Undirected-Graph-𝔽 :
    {y : vertex-Undirected-Graph-𝔽 G} (w : walk-Undirected-Graph-𝔽 G x y) →
    (v : vertex-on-walk-Undirected-Graph-𝔽 G w) →
    vertex-Undirected-Graph-𝔽 G → UU l1
  is-vertex-on-first-segment-walk-Undirected-Graph-𝔽 w v =
    is-vertex-on-walk-Undirected-Graph-𝔽 G
      ( first-segment-walk-Undirected-Graph-𝔽 G w v)

  is-vertex-on-second-segment-walk-Undirected-Graph-𝔽 :
    {y : vertex-Undirected-Graph-𝔽 G} (w : walk-Undirected-Graph-𝔽 G x y) →
    (v : vertex-on-walk-Undirected-Graph-𝔽 G w) →
    vertex-Undirected-Graph-𝔽 G → UU l1
  is-vertex-on-second-segment-walk-Undirected-Graph-𝔽 w v =
    is-vertex-on-walk-Undirected-Graph-𝔽 G
      ( second-segment-walk-Undirected-Graph-𝔽 G w v)

  is-vertex-on-first-or-second-segment-walk-Undirected-Graph-𝔽 :
    {y : vertex-Undirected-Graph-𝔽 G} (w : walk-Undirected-Graph-𝔽 G x y) →
    (u v : vertex-on-walk-Undirected-Graph-𝔽 G w) →
    ( is-vertex-on-first-segment-walk-Undirected-Graph-𝔽 w u
      ( vertex-vertex-on-walk-Undirected-Graph-𝔽 G w v)) +
    ( is-vertex-on-second-segment-walk-Undirected-Graph-𝔽 w u
      ( vertex-vertex-on-walk-Undirected-Graph-𝔽 G w v))
  is-vertex-on-first-or-second-segment-walk-Undirected-Graph-𝔽 =
    is-vertex-on-first-or-second-segment-walk-Undirected-Graph
      ( undirected-graph-Undirected-Graph-𝔽 G)
```

### For any decomposition of a walk `w` into `w1` followed by `w2`, any vertex on `w1` is a vertex on `w`

```agda
is-vertex-on-walk-is-vertex-on-first-segment-walk-Undirected-Graph-𝔽 :
  {l1 l2 : Level} (G : Undirected-Graph-𝔽 l1 l2)
  {x y : vertex-Undirected-Graph-𝔽 G}
  (w : walk-Undirected-Graph-𝔽 G x y)
  (v : vertex-on-walk-Undirected-Graph-𝔽 G w)
  (u : vertex-Undirected-Graph-𝔽 G) →
  is-vertex-on-first-segment-walk-Undirected-Graph-𝔽 G w v u →
  is-vertex-on-walk-Undirected-Graph-𝔽 G w u
is-vertex-on-walk-is-vertex-on-first-segment-walk-Undirected-Graph-𝔽 G =
  is-vertex-on-walk-is-vertex-on-first-segment-walk-Undirected-Graph
    ( undirected-graph-Undirected-Graph-𝔽 G)
```

### For any decomposition of a walk `w` into `w1` followed by `w2`, any vertex on `w2` is a vertex on `w`

```agda
is-vertex-on-walk-is-vertex-on-second-segment-walk-Undirected-Graph-𝔽 :
  {l1 l2 : Level} (G : Undirected-Graph-𝔽 l1 l2)
  {x y : vertex-Undirected-Graph-𝔽 G}
  (w : walk-Undirected-Graph-𝔽 G x y)
  (v : vertex-on-walk-Undirected-Graph-𝔽 G w)
  (u : vertex-Undirected-Graph-𝔽 G) →
  is-vertex-on-second-segment-walk-Undirected-Graph-𝔽 G w v u →
  is-vertex-on-walk-Undirected-Graph-𝔽 G w u
is-vertex-on-walk-is-vertex-on-second-segment-walk-Undirected-Graph-𝔽 G =
  is-vertex-on-walk-is-vertex-on-second-segment-walk-Undirected-Graph
    ( undirected-graph-Undirected-Graph-𝔽 G)
```

### Constant walks are identifications

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph-𝔽 l1 l2)
  {x : vertex-Undirected-Graph-𝔽 G}
  where

  is-constant-walk-Undirected-Graph-𝔽-Prop :
    {y : vertex-Undirected-Graph-𝔽 G} →
    walk-Undirected-Graph-𝔽 G x y → Prop lzero
  is-constant-walk-Undirected-Graph-𝔽-Prop =
    is-constant-walk-Undirected-Graph-Prop
      ( undirected-graph-Undirected-Graph-𝔽 G)

  is-constant-walk-Undirected-Graph-𝔽 :
    {y : vertex-Undirected-Graph-𝔽 G} →
    walk-Undirected-Graph-𝔽 G x y → UU lzero
  is-constant-walk-Undirected-Graph-𝔽 =
    is-constant-walk-Undirected-Graph (undirected-graph-Undirected-Graph-𝔽 G)

  constant-walk-Undirected-Graph-𝔽 :
    (y : vertex-Undirected-Graph-𝔽 G) → UU (lsuc lzero ⊔ l1 ⊔ l2)
  constant-walk-Undirected-Graph-𝔽 =
    constant-walk-Undirected-Graph (undirected-graph-Undirected-Graph-𝔽 G) {x}

  is-decidable-is-constant-walk-Undirected-Graph-𝔽 :
    {y : vertex-Undirected-Graph-𝔽 G} (w : walk-Undirected-Graph-𝔽 G x y) →
    is-decidable (is-constant-walk-Undirected-Graph-𝔽 w)
  is-decidable-is-constant-walk-Undirected-Graph-𝔽 =
    is-decidable-is-constant-walk-Undirected-Graph
      ( undirected-graph-Undirected-Graph-𝔽 G)

  refl-constant-walk-Undirected-Graph-𝔽 :
    constant-walk-Undirected-Graph-𝔽 x
  refl-constant-walk-Undirected-Graph-𝔽 =
    refl-constant-walk-Undirected-Graph (undirected-graph-Undirected-Graph-𝔽 G)

  is-contr-total-constant-walk-Undirected-Graph-𝔽 :
    is-contr (Σ (vertex-Undirected-Graph-𝔽 G) constant-walk-Undirected-Graph-𝔽)
  is-contr-total-constant-walk-Undirected-Graph-𝔽 =
    is-contr-total-constant-walk-Undirected-Graph
      ( undirected-graph-Undirected-Graph-𝔽 G)

  constant-walk-eq-Undirected-Graph-𝔽 :
    (y : vertex-Undirected-Graph-𝔽 G) →
    x ＝ y → constant-walk-Undirected-Graph-𝔽 y
  constant-walk-eq-Undirected-Graph-𝔽 =
    constant-walk-eq-Undirected-Graph (undirected-graph-Undirected-Graph-𝔽 G)

  is-equiv-constant-walk-eq-Undirected-Graph-𝔽 :
    (y : vertex-Undirected-Graph-𝔽 G) →
    is-equiv (constant-walk-eq-Undirected-Graph-𝔽 y)
  is-equiv-constant-walk-eq-Undirected-Graph-𝔽 =
    is-equiv-constant-walk-eq-Undirected-Graph
      ( undirected-graph-Undirected-Graph-𝔽 G)

  equiv-constant-walk-eq-Undirected-Graph-𝔽 :
    (y : vertex-Undirected-Graph-𝔽 G) →
    (x ＝ y) ≃ constant-walk-Undirected-Graph-𝔽 y
  equiv-constant-walk-eq-Undirected-Graph-𝔽 =
    equiv-constant-walk-eq-Undirected-Graph
      ( undirected-graph-Undirected-Graph-𝔽 G)

  eq-constant-walk-Undirected-Graph-𝔽 :
    {y : vertex-Undirected-Graph-𝔽 G} →
    constant-walk-Undirected-Graph-𝔽 y → x ＝ y
  eq-constant-walk-Undirected-Graph-𝔽 =
    eq-constant-walk-Undirected-Graph (undirected-graph-Undirected-Graph-𝔽 G)

  is-prop-constant-walk-Undirected-Graph-𝔽 :
    (y : vertex-Undirected-Graph-𝔽 G) →
    is-prop (constant-walk-Undirected-Graph-𝔽 y)
  is-prop-constant-walk-Undirected-Graph-𝔽 y =
    is-prop-equiv'
      ( equiv-constant-walk-eq-Undirected-Graph-𝔽 y)
      ( is-set-vertex-Undirected-Graph-𝔽 G x y)

  is-decidable-constant-walk-Undirected-Graph-𝔽 :
    (y : vertex-Undirected-Graph-𝔽 G) →
    is-decidable (constant-walk-Undirected-Graph-𝔽 y)
  is-decidable-constant-walk-Undirected-Graph-𝔽 y =
    is-decidable-equiv'
      ( equiv-constant-walk-eq-Undirected-Graph-𝔽 y)
      ( has-decidable-equality-vertex-Undirected-Graph-𝔽 G x y)

  is-decidable-prop-constant-walk-Undirected-Graph-𝔽 :
    (y : vertex-Undirected-Graph-𝔽 G) →
    is-decidable-prop (constant-walk-Undirected-Graph-𝔽 y)
  pr1 (is-decidable-prop-constant-walk-Undirected-Graph-𝔽 y) =
    is-prop-constant-walk-Undirected-Graph-𝔽 y
  pr2 (is-decidable-prop-constant-walk-Undirected-Graph-𝔽 y) =
    is-decidable-constant-walk-Undirected-Graph-𝔽 y
```

### The type of walks from `x` to `y` in a finite undirected graph has decidable equality

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph-𝔽 l1 l2)
  where

  has-decidable-equality-walk-Undirected-Graph-𝔽 :
    {x y : vertex-Undirected-Graph-𝔽 G} →
    has-decidable-equality (walk-Undirected-Graph-𝔽 G x y)
  has-decidable-equality-walk-Undirected-Graph-𝔽 {x} {.x}
    refl-walk-Undirected-Graph w =

    {!!}
  has-decidable-equality-walk-Undirected-Graph-𝔽 {x} {._}
    ( cons-walk-Undirected-Graph p e v) w =
    {!!}
```
