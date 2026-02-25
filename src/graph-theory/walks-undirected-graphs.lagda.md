# Walks in undirected graphs

```agda
module graph-theory.walks-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-coproduct-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.undirected-graphs

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A
{{#concept "walk" Disambiguation="in an undirected graph" WD="walk" WDID=Q12776184 Agda=walk-Undirected-Graph}}
in an [undirected graph](graph-theory.undirected-graphs.md) consists of a
[list](lists.lists.md) of edges that connect the starting point with the end
point. Walks may repeat edges and pass through the same vertex multiple times.

## Definitions

### Walks in undirected graphs

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  data
    walk-Undirected-Graph (x : vertex-Undirected-Graph G) :
      vertex-Undirected-Graph G → UU (l1 ⊔ l2 ⊔ lsuc lzero)
      where
      refl-walk-Undirected-Graph : walk-Undirected-Graph x x
      cons-walk-Undirected-Graph :
        (p : unordered-pair (vertex-Undirected-Graph G)) →
        (e : edge-Undirected-Graph G p) →
        {y : type-unordered-pair p} →
        walk-Undirected-Graph x (element-unordered-pair p y) →
        walk-Undirected-Graph x (other-element-unordered-pair p y)
```

### The vertices on a walk

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  is-vertex-on-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    vertex-Undirected-Graph G → UU l1
  is-vertex-on-walk-Undirected-Graph refl-walk-Undirected-Graph v = x ＝ v
  is-vertex-on-walk-Undirected-Graph (cons-walk-Undirected-Graph p e {y} w) v =
    ( is-vertex-on-walk-Undirected-Graph w v) +
    ( other-element-unordered-pair p y ＝ v)

  vertex-on-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) → UU l1
  vertex-on-walk-Undirected-Graph w =
    Σ (vertex-Undirected-Graph G) (is-vertex-on-walk-Undirected-Graph w)

  vertex-vertex-on-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    vertex-on-walk-Undirected-Graph w → vertex-Undirected-Graph G
  vertex-vertex-on-walk-Undirected-Graph w = pr1
```

### Edges on a walk

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  is-edge-on-walk-Undirected-Graph' :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    total-edge-Undirected-Graph G → UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-edge-on-walk-Undirected-Graph' refl-walk-Undirected-Graph e =
    raise-empty (lsuc lzero ⊔ l1 ⊔ l2)
  is-edge-on-walk-Undirected-Graph' (cons-walk-Undirected-Graph q f w) e =
    ( is-edge-on-walk-Undirected-Graph' w e) +
    ( pair q f ＝ e)

  is-edge-on-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    (p : unordered-pair-vertices-Undirected-Graph G) →
    edge-Undirected-Graph G p → UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-edge-on-walk-Undirected-Graph w p e =
    is-edge-on-walk-Undirected-Graph' w (pair p e)

  edge-on-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    UU (lsuc lzero ⊔ l1 ⊔ l2)
  edge-on-walk-Undirected-Graph w =
    Σ ( total-edge-Undirected-Graph G)
      ( λ e → is-edge-on-walk-Undirected-Graph' w e)

  edge-edge-on-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    edge-on-walk-Undirected-Graph w → total-edge-Undirected-Graph G
  edge-edge-on-walk-Undirected-Graph w = pr1
```

### Concatenating walks

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  concat-walk-Undirected-Graph :
    {y z : vertex-Undirected-Graph G} →
    walk-Undirected-Graph G x y → walk-Undirected-Graph G y z →
    walk-Undirected-Graph G x z
  concat-walk-Undirected-Graph w refl-walk-Undirected-Graph = w
  concat-walk-Undirected-Graph w (cons-walk-Undirected-Graph p e v) =
    cons-walk-Undirected-Graph p e (concat-walk-Undirected-Graph w v)
```

### The length of a walk

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  length-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} → walk-Undirected-Graph G x y → ℕ
  length-walk-Undirected-Graph refl-walk-Undirected-Graph = 0
  length-walk-Undirected-Graph (cons-walk-Undirected-Graph p e w) =
    succ-ℕ (length-walk-Undirected-Graph w)
```

## Properties

### The type of vertices on the constant walk is contractible

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) (x : vertex-Undirected-Graph G)
  where

  is-contr-vertex-on-walk-refl-walk-Undirected-Graph :
    is-contr
      ( vertex-on-walk-Undirected-Graph G (refl-walk-Undirected-Graph {x = x}))
  is-contr-vertex-on-walk-refl-walk-Undirected-Graph =
    is-torsorial-Id x
```

### The type of vertices on a walk is equivalent to `Fin (n + 1)` where `n` is the length of the walk

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  compute-vertex-on-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    vertex-on-walk-Undirected-Graph G w ≃
    Fin (succ-ℕ (length-walk-Undirected-Graph G w))
  compute-vertex-on-walk-Undirected-Graph refl-walk-Undirected-Graph =
    equiv-is-contr
      ( is-contr-vertex-on-walk-refl-walk-Undirected-Graph G x)
      ( is-contr-Fin-1)
  compute-vertex-on-walk-Undirected-Graph
    ( cons-walk-Undirected-Graph p e {y} w) =
    ( equiv-coproduct
      ( compute-vertex-on-walk-Undirected-Graph w)
      ( equiv-is-contr
        ( is-torsorial-Id (other-element-unordered-pair p y))
        ( is-contr-unit))) ∘e
    ( left-distributive-Σ-coproduct)
```

### The type of edges on a constant walk is empty

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) (x : vertex-Undirected-Graph G)
  where

  is-empty-edge-on-walk-refl-walk-Undirected-Graph :
    is-empty
      ( edge-on-walk-Undirected-Graph G (refl-walk-Undirected-Graph {x = x}))
  is-empty-edge-on-walk-refl-walk-Undirected-Graph = is-empty-raise-empty ∘ pr2
```

### The type of edges on a walk is equivalent to `Fin n` where `n` is the length of the walk

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  compute-edge-on-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    edge-on-walk-Undirected-Graph G w ≃ Fin (length-walk-Undirected-Graph G w)
  compute-edge-on-walk-Undirected-Graph refl-walk-Undirected-Graph =
    equiv-is-empty
      ( is-empty-edge-on-walk-refl-walk-Undirected-Graph G x)
      ( id)
  compute-edge-on-walk-Undirected-Graph (cons-walk-Undirected-Graph p e w) =
    ( equiv-coproduct
      ( compute-edge-on-walk-Undirected-Graph w)
      ( equiv-is-contr
        ( is-torsorial-Id (pair p e))
        ( is-contr-unit))) ∘e
    ( left-distributive-Σ-coproduct)
```

### Right unit law for concatenation of walks

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  right-unit-law-concat-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    (concat-walk-Undirected-Graph G w refl-walk-Undirected-Graph) ＝ w
  right-unit-law-concat-walk-Undirected-Graph refl-walk-Undirected-Graph = refl
  right-unit-law-concat-walk-Undirected-Graph
    ( cons-walk-Undirected-Graph p e w) =
    ap
      ( cons-walk-Undirected-Graph p e)
      ( right-unit-law-concat-walk-Undirected-Graph w)
```

### For any walk `w` from `x` to `y` and any vertex `v` on `w`, we can decompose `w` into a walk `w1` from `x` to `v` and a walk `w2` from `v` to `y`

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  first-segment-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y)
    (v : vertex-on-walk-Undirected-Graph G w) →
    walk-Undirected-Graph G x (vertex-vertex-on-walk-Undirected-Graph G w v)
  first-segment-walk-Undirected-Graph
    refl-walk-Undirected-Graph (v , refl) = refl-walk-Undirected-Graph
  first-segment-walk-Undirected-Graph
    (cons-walk-Undirected-Graph p e w) (v , inl x) =
    first-segment-walk-Undirected-Graph w (pair v x)
  first-segment-walk-Undirected-Graph
    ( cons-walk-Undirected-Graph p e w)
    ( .(other-element-unordered-pair p _) , inr refl) =
    cons-walk-Undirected-Graph p e w

  second-segment-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y)
    (v : vertex-on-walk-Undirected-Graph G w) →
    walk-Undirected-Graph G (vertex-vertex-on-walk-Undirected-Graph G w v) y
  second-segment-walk-Undirected-Graph
    refl-walk-Undirected-Graph (v , refl) = refl-walk-Undirected-Graph
  second-segment-walk-Undirected-Graph
    (cons-walk-Undirected-Graph p e w) (v , inl H) =
    cons-walk-Undirected-Graph p e
      ( second-segment-walk-Undirected-Graph w (pair v H))
  second-segment-walk-Undirected-Graph
    ( cons-walk-Undirected-Graph p e w)
    ( .(other-element-unordered-pair p _) , inr refl) =
    refl-walk-Undirected-Graph

  eq-decompose-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y)
    (v : vertex-on-walk-Undirected-Graph G w) →
    ( concat-walk-Undirected-Graph G
      ( first-segment-walk-Undirected-Graph w v)
      ( second-segment-walk-Undirected-Graph w v)) ＝ w
  eq-decompose-walk-Undirected-Graph refl-walk-Undirected-Graph (v , refl) =
    refl
  eq-decompose-walk-Undirected-Graph
    ( cons-walk-Undirected-Graph p e w) (v , inl H) =
    ap
      ( cons-walk-Undirected-Graph p e)
      ( eq-decompose-walk-Undirected-Graph w (pair v H))
  eq-decompose-walk-Undirected-Graph
    ( cons-walk-Undirected-Graph p e w)
    ( .(other-element-unordered-pair p _) , inr refl) =
    right-unit-law-concat-walk-Undirected-Graph G
      ( cons-walk-Undirected-Graph p e w)
```

### For any edge `e` on `p`, if `v` is a vertex on `w` then it is a vertex on `cons p e w`

```agda
is-vertex-on-walk-cons-walk-Undirected-Graph :
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  (p : unordered-pair-vertices-Undirected-Graph G)
  (e : edge-Undirected-Graph G p) →
  {x : vertex-Undirected-Graph G} {y : type-unordered-pair p} →
  (w : walk-Undirected-Graph G x (element-unordered-pair p y)) →
  {v : vertex-Undirected-Graph G} →
  is-vertex-on-walk-Undirected-Graph G w v →
  is-vertex-on-walk-Undirected-Graph G (cons-walk-Undirected-Graph p e w) v
is-vertex-on-walk-cons-walk-Undirected-Graph G p e w = inl
```

### For any decomposition of a walk `w` into `w1` followed by `w2`, any vertex on `w` is a vertex on `w1` or on `w2`

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  is-vertex-on-first-segment-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    (v : vertex-on-walk-Undirected-Graph G w) →
    vertex-Undirected-Graph G → UU l1
  is-vertex-on-first-segment-walk-Undirected-Graph w v =
    is-vertex-on-walk-Undirected-Graph G
      ( first-segment-walk-Undirected-Graph G w v)

  is-vertex-on-second-segment-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    (v : vertex-on-walk-Undirected-Graph G w) →
    vertex-Undirected-Graph G → UU l1
  is-vertex-on-second-segment-walk-Undirected-Graph w v =
    is-vertex-on-walk-Undirected-Graph G
      ( second-segment-walk-Undirected-Graph G w v)

  is-vertex-on-first-or-second-segment-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    (u v : vertex-on-walk-Undirected-Graph G w) →
    ( is-vertex-on-first-segment-walk-Undirected-Graph w u
      ( vertex-vertex-on-walk-Undirected-Graph G w v)) +
    ( is-vertex-on-second-segment-walk-Undirected-Graph w u
      ( vertex-vertex-on-walk-Undirected-Graph G w v))
  is-vertex-on-first-or-second-segment-walk-Undirected-Graph
    refl-walk-Undirected-Graph (u , refl) (.u , refl) =
    inl refl
  is-vertex-on-first-or-second-segment-walk-Undirected-Graph
    ( cons-walk-Undirected-Graph p e w) (u , inl H) (v , inl K) =
    map-coproduct id
      ( is-vertex-on-walk-cons-walk-Undirected-Graph G p e
        ( second-segment-walk-Undirected-Graph G w (u , H)))
      ( is-vertex-on-first-or-second-segment-walk-Undirected-Graph w
        ( pair u H)
        ( pair v K))
  is-vertex-on-first-or-second-segment-walk-Undirected-Graph
    ( cons-walk-Undirected-Graph p e w)
    ( u , inl H)
    ( .(other-element-unordered-pair p _) , inr refl) =
    inr (inr refl)
  is-vertex-on-first-or-second-segment-walk-Undirected-Graph
    ( cons-walk-Undirected-Graph p e w)
    ( .(other-element-unordered-pair p _) , inr refl)
    ( v , inl x) =
    inl (is-vertex-on-walk-cons-walk-Undirected-Graph G p e w x)
  is-vertex-on-first-or-second-segment-walk-Undirected-Graph
    ( cons-walk-Undirected-Graph p e w)
    ( .(other-element-unordered-pair p _) , inr refl)
    ( .(other-element-unordered-pair p _) , inr refl) =
    inl (inr refl)
```

### For any decomposition of a walk `w` into `w1` followed by `w2`, any vertex on `w1` is a vertex on `w`

```agda
is-vertex-on-walk-is-vertex-on-first-segment-walk-Undirected-Graph :
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x y : vertex-Undirected-Graph G}
  (w : walk-Undirected-Graph G x y) (v : vertex-on-walk-Undirected-Graph G w)
  (u : vertex-Undirected-Graph G) →
  is-vertex-on-first-segment-walk-Undirected-Graph G w v u →
  is-vertex-on-walk-Undirected-Graph G w u
is-vertex-on-walk-is-vertex-on-first-segment-walk-Undirected-Graph G
  refl-walk-Undirected-Graph
  (v , refl)
  .(vertex-vertex-on-walk-Undirected-Graph G refl-walk-Undirected-Graph
    (v , refl))
  refl =
  refl
is-vertex-on-walk-is-vertex-on-first-segment-walk-Undirected-Graph G
  ( cons-walk-Undirected-Graph p e w) (v , inl K) u H =
  inl
    ( is-vertex-on-walk-is-vertex-on-first-segment-walk-Undirected-Graph
      G w (pair v K) u H)
is-vertex-on-walk-is-vertex-on-first-segment-walk-Undirected-Graph G
  ( cons-walk-Undirected-Graph p e w)
  (.(other-element-unordered-pair p _) , inr refl) u H =
  H
```

### For any decomposition of a walk `w` into `w1` followed by `w2`, any vertex on `w2` is a vertex on `w`

```agda
is-vertex-on-walk-is-vertex-on-second-segment-walk-Undirected-Graph :
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x y : vertex-Undirected-Graph G}
  (w : walk-Undirected-Graph G x y) (v : vertex-on-walk-Undirected-Graph G w)
  (u : vertex-Undirected-Graph G) →
  is-vertex-on-second-segment-walk-Undirected-Graph G w v u →
  is-vertex-on-walk-Undirected-Graph G w u
is-vertex-on-walk-is-vertex-on-second-segment-walk-Undirected-Graph
  G refl-walk-Undirected-Graph (v , refl) .v refl = refl
is-vertex-on-walk-is-vertex-on-second-segment-walk-Undirected-Graph
  G (cons-walk-Undirected-Graph p e w) (v , inl K) u (inl H) =
  is-vertex-on-walk-cons-walk-Undirected-Graph G p e w
    ( is-vertex-on-walk-is-vertex-on-second-segment-walk-Undirected-Graph
      G w (pair v K) u H)
is-vertex-on-walk-is-vertex-on-second-segment-walk-Undirected-Graph G
  ( cons-walk-Undirected-Graph p e w)
  ( v , inl K)
  .(other-element-unordered-pair p _)
  ( inr refl) =
  inr refl
is-vertex-on-walk-is-vertex-on-second-segment-walk-Undirected-Graph G
  ( cons-walk-Undirected-Graph p e w)
  ( .(other-element-unordered-pair p _) , inr refl)
  .(other-element-unordered-pair p _)
  ( refl) =
  inr refl
```

### Constant walks are identifications

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2) {x : vertex-Undirected-Graph G}
  where

  is-constant-walk-Undirected-Graph-Prop :
    {y : vertex-Undirected-Graph G} →
    walk-Undirected-Graph G x y → Prop lzero
  is-constant-walk-Undirected-Graph-Prop w =
    is-zero-ℕ-Prop (length-walk-Undirected-Graph G w)

  is-constant-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} → walk-Undirected-Graph G x y → UU lzero
  is-constant-walk-Undirected-Graph w =
    type-Prop (is-constant-walk-Undirected-Graph-Prop w)

  constant-walk-Undirected-Graph :
    (y : vertex-Undirected-Graph G) → UU (lsuc lzero ⊔ l1 ⊔ l2)
  constant-walk-Undirected-Graph y =
    Σ (walk-Undirected-Graph G x y) is-constant-walk-Undirected-Graph

  is-decidable-is-constant-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} (w : walk-Undirected-Graph G x y) →
    is-decidable (is-constant-walk-Undirected-Graph w)
  is-decidable-is-constant-walk-Undirected-Graph w =
    is-decidable-is-zero-ℕ (length-walk-Undirected-Graph G w)

  refl-constant-walk-Undirected-Graph :
    constant-walk-Undirected-Graph x
  pr1 refl-constant-walk-Undirected-Graph = refl-walk-Undirected-Graph
  pr2 refl-constant-walk-Undirected-Graph = refl

  is-torsorial-constant-walk-Undirected-Graph :
    is-torsorial constant-walk-Undirected-Graph
  pr1 (pr1 is-torsorial-constant-walk-Undirected-Graph) = x
  pr2 (pr1 is-torsorial-constant-walk-Undirected-Graph) =
    refl-constant-walk-Undirected-Graph
  pr2 is-torsorial-constant-walk-Undirected-Graph
    (v , refl-walk-Undirected-Graph , refl) =
    refl
  pr2 is-torsorial-constant-walk-Undirected-Graph
    (.(other-element-unordered-pair p _) ,
      cons-walk-Undirected-Graph p e w , ())

  constant-walk-eq-Undirected-Graph :
    (y : vertex-Undirected-Graph G) → x ＝ y → constant-walk-Undirected-Graph y
  constant-walk-eq-Undirected-Graph y refl = refl-constant-walk-Undirected-Graph

  is-equiv-constant-walk-eq-Undirected-Graph :
    (y : vertex-Undirected-Graph G) →
    is-equiv (constant-walk-eq-Undirected-Graph y)
  is-equiv-constant-walk-eq-Undirected-Graph =
    fundamental-theorem-id
      ( is-torsorial-constant-walk-Undirected-Graph)
      ( constant-walk-eq-Undirected-Graph)

  equiv-constant-walk-eq-Undirected-Graph :
    (y : vertex-Undirected-Graph G) →
    (x ＝ y) ≃ constant-walk-Undirected-Graph y
  pr1 (equiv-constant-walk-eq-Undirected-Graph y) =
    constant-walk-eq-Undirected-Graph y
  pr2 (equiv-constant-walk-eq-Undirected-Graph y) =
    is-equiv-constant-walk-eq-Undirected-Graph y

  eq-constant-walk-Undirected-Graph :
    {y : vertex-Undirected-Graph G} → constant-walk-Undirected-Graph y → x ＝ y
  eq-constant-walk-Undirected-Graph {y} =
    map-inv-is-equiv (is-equiv-constant-walk-eq-Undirected-Graph y)
```

## External links

- [Path](https://www.wikidata.org/entity/Q917421) on Wikidata
- [Path (graph theory)](<https://en.wikipedia.org/wiki/Path_(graph_theory)>) at
  Wikipedia
- [Walk](https://mathworld.wolfram.com/Walk.html) at Wolfram MathWorld
