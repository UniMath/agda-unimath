---
title: The underlying graphs of elements of W-types
---

```agda
module foundation.underlying-graphs-of-elements-w-types where

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.elementhood-relation-w-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.embeddings
open import foundation.empty-types
open import foundation.fibers-of-maps
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.w-types

open import graph-theory.directed-graphs
open import graph-theory.directed-trees
open import graph-theory.morphisms-directed-graphs
open import graph-theory.trails-directed-graphs
open import graph-theory.walks-directed-graphs
```

## Idea

We assign to each element of a W-type `𝕎 A B` a directed graph. This directed graph is a tree in the graph theoretical sense if and only if each `B x` is a type with decidable equality.


## Definition

### The type of nodes of the underlying graph of an element of a W-type

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  data node-graph-element-𝕎 : 𝕎 A B → UU (l1 ⊔ l2) where
    root-𝕎 :
      {w : 𝕎 A B} → node-graph-element-𝕎 w
    node-inclusion-graph-element-𝕎 :
      {u v : 𝕎 A B} → (u ∈-𝕎 v) →
      node-graph-element-𝕎 u → node-graph-element-𝕎 v

  data edge-graph-element-𝕎 :
    (w : 𝕎 A B) (x y : node-graph-element-𝕎 w) → UU (l1 ⊔ l2)
    where
    edge-to-root-graph-element-𝕎 :
      {u v : 𝕎 A B} (H : u ∈-𝕎 v) →
      edge-graph-element-𝕎 v
        ( node-inclusion-graph-element-𝕎 H root-𝕎)
        ( root-𝕎)
    edge-inclusion-graph-element-𝕎 :
      {u v : 𝕎 A B} (H : u ∈-𝕎 v) →
      {x y : node-graph-element-𝕎 u} (e : edge-graph-element-𝕎 u x y) →
      edge-graph-element-𝕎 v
        ( node-inclusion-graph-element-𝕎 H x)
        ( node-inclusion-graph-element-𝕎 H y)

  graph-element-𝕎 : 𝕎 A B → Graph (l1 ⊔ l2) (l1 ⊔ l2)
  pr1 (graph-element-𝕎 w) = node-graph-element-𝕎 w
  pr2 (graph-element-𝕎 w) = edge-graph-element-𝕎 w
```

## Properties

### To be a root is decidable

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-root-node-graph-element-𝕎 :
    (w : 𝕎 A B) (x : node-graph-element-𝕎 w) → UU (l1 ⊔ l2)
  is-root-node-graph-element-𝕎 w x = root-𝕎 ＝ x

  is-decidable-is-root-node-graph-element-𝕎 :
    (w : 𝕎 A B) (x : node-graph-element-𝕎 w) →
    is-decidable (is-root-node-graph-element-𝕎 w x)
  is-decidable-is-root-node-graph-element-𝕎 w root-𝕎 = inl refl
  is-decidable-is-root-node-graph-element-𝕎 w
    ( node-inclusion-graph-element-𝕎 H y) =
    inr (λ ())
```

### Characterization of equality of the type of nodes of the underlying graph of an element of `𝕎 A B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  data Eq-node-graph-element-𝕎 (w : 𝕎 A B) :
    (x y : node-graph-element-𝕎 w) → UU (l1 ⊔ l2)
    where
    root-refl-Eq-node-graph-element-𝕎 :
      Eq-node-graph-element-𝕎 w root-𝕎 root-𝕎
    node-inclusion-Eq-node-graph-element-𝕎 :
      {u : 𝕎 A B} (H : u ∈-𝕎 w) {x y : node-graph-element-𝕎 u} →
      Eq-node-graph-element-𝕎 u x y →
      Eq-node-graph-element-𝕎 w
        ( node-inclusion-graph-element-𝕎 H x)
        ( node-inclusion-graph-element-𝕎 H y)

  refl-Eq-node-graph-element-𝕎 :
    {w : 𝕎 A B} (x : node-graph-element-𝕎 w) →
    Eq-node-graph-element-𝕎 w x x
  refl-Eq-node-graph-element-𝕎 root-𝕎 = root-refl-Eq-node-graph-element-𝕎
  refl-Eq-node-graph-element-𝕎 (node-inclusion-graph-element-𝕎 {u} H x) =
    node-inclusion-Eq-node-graph-element-𝕎 H (refl-Eq-node-graph-element-𝕎 x)

  center-total-Eq-node-graph-element-𝕎 :
    {w : 𝕎 A B} (x : node-graph-element-𝕎 w) →
    Σ (node-graph-element-𝕎 w) (Eq-node-graph-element-𝕎 w x)
  pr1 (center-total-Eq-node-graph-element-𝕎 x) = x
  pr2 (center-total-Eq-node-graph-element-𝕎 x) =
    refl-Eq-node-graph-element-𝕎 x

  contraction-total-Eq-node-graph-element-𝕎 :
    {w : 𝕎 A B} (x : node-graph-element-𝕎 w) →
    (u : Σ (node-graph-element-𝕎 w) (Eq-node-graph-element-𝕎 w x)) →
    center-total-Eq-node-graph-element-𝕎 x ＝ u
  contraction-total-Eq-node-graph-element-𝕎 .root-𝕎
    (.root-𝕎 , root-refl-Eq-node-graph-element-𝕎) =
    refl
  contraction-total-Eq-node-graph-element-𝕎
    .(node-inclusion-graph-element-𝕎 H _)
    ( .(node-inclusion-graph-element-𝕎 H _) ,
      node-inclusion-Eq-node-graph-element-𝕎 H e) =
    ap
      ( map-Σ
        ( λ z → Eq-node-graph-element-𝕎 _ _ z)
        ( node-inclusion-graph-element-𝕎 H)
        ( λ y → node-inclusion-Eq-node-graph-element-𝕎 H))
      ( contraction-total-Eq-node-graph-element-𝕎 _ (_ , e))

  is-contr-total-Eq-node-graph-element-𝕎 :
    (w : 𝕎 A B) (x : node-graph-element-𝕎 w) →
    is-contr (Σ (node-graph-element-𝕎 w) (Eq-node-graph-element-𝕎 w x))
  pr1 (is-contr-total-Eq-node-graph-element-𝕎 w x) =
    center-total-Eq-node-graph-element-𝕎 x
  pr2 (is-contr-total-Eq-node-graph-element-𝕎 w x) =
    contraction-total-Eq-node-graph-element-𝕎 x

  Eq-eq-node-graph-element-𝕎 :
    (w : 𝕎 A B) {x y : node-graph-element-𝕎 w} →
    x ＝ y → Eq-node-graph-element-𝕎 w x y
  Eq-eq-node-graph-element-𝕎 w refl = refl-Eq-node-graph-element-𝕎 _

  is-equiv-Eq-eq-node-graph-element-𝕎 :
    (w : 𝕎 A B) (x y : node-graph-element-𝕎 w) →
    is-equiv (Eq-eq-node-graph-element-𝕎 w {x} {y})
  is-equiv-Eq-eq-node-graph-element-𝕎 w x =
    fundamental-theorem-id
      ( is-contr-total-Eq-node-graph-element-𝕎 w x)
      ( λ y → Eq-eq-node-graph-element-𝕎 w {x} {y})

  extensionality-node-graph-element-𝕎 :
    (w : 𝕎 A B) (x y : node-graph-element-𝕎 w) →
    (x ＝ y) ≃ Eq-node-graph-element-𝕎 w x y
  pr1 (extensionality-node-graph-element-𝕎 w x y) =
    Eq-eq-node-graph-element-𝕎 w {x} {y}
  pr2 (extensionality-node-graph-element-𝕎 w x y) =
    is-equiv-Eq-eq-node-graph-element-𝕎 w x y

  eq-Eq-node-graph-element-𝕎 :
    (w : 𝕎 A B) (x y : node-graph-element-𝕎 w) →
    Eq-node-graph-element-𝕎 w x y → x ＝ y
  eq-Eq-node-graph-element-𝕎 w x y =
    map-inv-equiv (extensionality-node-graph-element-𝕎 w x y)
```

### The type of nodes of the underlying graph of an element of a W-type is a coproduct

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  node-graph-element-𝕎' : 𝕎 A B → UU (l1 ⊔ l2)
  node-graph-element-𝕎' (tree-𝕎 x α) =
    Σ (B x) (λ y → node-graph-element-𝕎' (α y)) + unit

  map-compute-node-graph-element-𝕎 :
    (w : 𝕎 A B) → node-graph-element-𝕎 w → node-graph-element-𝕎' w
  map-compute-node-graph-element-𝕎 (tree-𝕎 x α) root-𝕎 = inr star
  map-compute-node-graph-element-𝕎
    ( tree-𝕎 x α)
    ( node-inclusion-graph-element-𝕎 (y , refl) n) =
    inl (pair y (map-compute-node-graph-element-𝕎 (α y) n))

  map-inv-compute-node-graph-element-𝕎 :
    (w : 𝕎 A B) → node-graph-element-𝕎' w → node-graph-element-𝕎 w
  map-inv-compute-node-graph-element-𝕎 (tree-𝕎 x α) (inl (y , n)) =
    node-inclusion-graph-element-𝕎
      ( pair y refl)
      ( map-inv-compute-node-graph-element-𝕎 (α y) n)
  map-inv-compute-node-graph-element-𝕎 (tree-𝕎 x α) (inr star) = root-𝕎

  issec-map-inv-compute-node-graph-element-𝕎 :
    (w : 𝕎 A B) →
    ( map-compute-node-graph-element-𝕎 w ∘
      map-inv-compute-node-graph-element-𝕎 w) ~ id
  issec-map-inv-compute-node-graph-element-𝕎 (tree-𝕎 x α) (inl (y , n)) =
    ap
      ( inl)
      ( eq-pair-Σ refl (issec-map-inv-compute-node-graph-element-𝕎 (α y) n))
  issec-map-inv-compute-node-graph-element-𝕎 (tree-𝕎 x α) (inr star) = refl

  isretr-map-inv-compute-node-graph-element-𝕎 :
    (w : 𝕎 A B) →
    ( map-inv-compute-node-graph-element-𝕎 w ∘
      map-compute-node-graph-element-𝕎 w) ~ id
  isretr-map-inv-compute-node-graph-element-𝕎 (tree-𝕎 x α) root-𝕎 = refl
  isretr-map-inv-compute-node-graph-element-𝕎
    ( tree-𝕎 x α)
    ( node-inclusion-graph-element-𝕎 (y , refl) n) =
    ap
      ( node-inclusion-graph-element-𝕎 (y , refl))
      ( isretr-map-inv-compute-node-graph-element-𝕎 (α y) n)

  is-equiv-map-compute-node-graph-element-𝕎 :
    (w : 𝕎 A B) → is-equiv (map-compute-node-graph-element-𝕎 w)
  is-equiv-map-compute-node-graph-element-𝕎 w =
    is-equiv-has-inverse
      ( map-inv-compute-node-graph-element-𝕎 w)
      ( issec-map-inv-compute-node-graph-element-𝕎 w)
      ( isretr-map-inv-compute-node-graph-element-𝕎 w)

  compute-node-graph-element-𝕎 :
    (w : 𝕎 A B) → node-graph-element-𝕎 w ≃ node-graph-element-𝕎' w
  pr1 (compute-node-graph-element-𝕎 w) = map-compute-node-graph-element-𝕎 w
  pr2 (compute-node-graph-element-𝕎 w) =
    is-equiv-map-compute-node-graph-element-𝕎 w
```

### The node-inclusion on the coproduct representation of the type of nodes

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  node-inclusion-graph-element-𝕎' :
    (v : 𝕎 A B) (y : B (symbol-𝕎 v)) →
    node-graph-element-𝕎' (component-𝕎 v y) → node-graph-element-𝕎' v
  node-inclusion-graph-element-𝕎' (tree-𝕎 x α) y n = inl (pair y n)
```

Note that it seems unreasonable to expect that `node-inclusion-graph-element-𝕎'` is an embedding. The total space `Σ (y : B x), node-graph-element-𝕎' (α y)` embeds into `node-graph-element-𝕎' (tree-𝕎 x α)`, and this implies that the node inclusion has the same truncation level as the fiber inclusions

```md
  node-graph-element-𝕎' (α b) → Σ (y : B x), node-graph-element-𝕎' (α y)
```

In other words, the fiber is `Ω (B , b)`.

### For any `u ∈-𝕎 v` in `𝕎 A B` we have a graph inclusion from the underlying graph of `u` to the underlying graph of `v`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  inclusion-graph-element-𝕎 :
    {u v : 𝕎 A B} → u ∈-𝕎 v →
    hom-Graph (graph-element-𝕎 u) (graph-element-𝕎 v)
  pr1 (inclusion-graph-element-𝕎 {u} {v} H) =
    node-inclusion-graph-element-𝕎 H
  pr2 (inclusion-graph-element-𝕎 {u} {v} H) x y e =
    edge-inclusion-graph-element-𝕎 H e
```

### The type of edges from the root of `u ∈-𝕎 v` to the root of `v` is contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-contr-edge-to-root-graph-element-𝕎 :
    {u v : 𝕎 A B} (H : u ∈-𝕎 v) →
    is-contr
      ( edge-graph-element-𝕎 v
        ( node-inclusion-graph-element-𝕎 H root-𝕎)
        ( root-𝕎))
  pr1 (is-contr-edge-to-root-graph-element-𝕎 H) =
    edge-to-root-graph-element-𝕎 H
  pr2
    ( is-contr-edge-to-root-graph-element-𝕎 H)
    ( edge-to-root-graph-element-𝕎 .H) =
    refl
```

### Computing the type of edges between nodes

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  root-𝕎' : (w : 𝕎 A B) → node-graph-element-𝕎' w
  root-𝕎' w = map-compute-node-graph-element-𝕎 w root-𝕎

  edge-graph-element-𝕎' :
    (v : 𝕎 A B) (x y : node-graph-element-𝕎' v) → UU (l1 ⊔ l2)
  edge-graph-element-𝕎' (tree-𝕎 a α) (inl (y , m)) (inl (z , n)) =
    Σ ( y ＝ z)
      ( λ p →
        edge-graph-element-𝕎' (α z) (tr node-graph-element-𝕎' (ap α p) m) n)
  edge-graph-element-𝕎' (tree-𝕎 a α) (inl (x , n)) (inr star) =
    n ＝ root-𝕎' (α x)
  edge-graph-element-𝕎' (tree-𝕎 a α) (inr star) (inl y) =
    raise-empty (l1 ⊔ l2)
  edge-graph-element-𝕎' (tree-𝕎 a α) (inr star) (inr star) =
    raise-empty (l1 ⊔ l2)

  root-map-compute-node-graph-element-𝕎 :
    (w : 𝕎 A B) →
    map-compute-node-graph-element-𝕎 w root-𝕎 ＝ root-𝕎' w
  root-map-compute-node-graph-element-𝕎 (tree-𝕎 a α) = refl

  map-compute-edge-graph-element-𝕎 :
    (v : 𝕎 A B) (x y : node-graph-element-𝕎 v) →
    edge-graph-element-𝕎 v x y →
    edge-graph-element-𝕎' v
      ( map-compute-node-graph-element-𝕎 v x)
      ( map-compute-node-graph-element-𝕎 v y)
  map-compute-edge-graph-element-𝕎
    ( tree-𝕎 a α)
    .( node-inclusion-graph-element-𝕎 (b , refl) root-𝕎)
    .( root-𝕎)
    ( edge-to-root-graph-element-𝕎 (b , refl)) =
    refl
  map-compute-edge-graph-element-𝕎
    ( tree-𝕎 x α)
    .( node-inclusion-graph-element-𝕎 (b , refl) _)
    .( node-inclusion-graph-element-𝕎 (b , refl) _)
    ( edge-inclusion-graph-element-𝕎 (b , refl) {m} {n} e) =
    (refl , map-compute-edge-graph-element-𝕎 (α b) m n e)

  map-inv-compute-edge-graph-element-𝕎 :
    ( v : 𝕎 A B) (x y : node-graph-element-𝕎 v) →
    edge-graph-element-𝕎' v
      ( map-compute-node-graph-element-𝕎 v x)
      ( map-compute-node-graph-element-𝕎 v y) → 
    edge-graph-element-𝕎 v x y
  map-inv-compute-edge-graph-element-𝕎 (tree-𝕎 a α) root-𝕎 root-𝕎 e =
    ex-falso (is-empty-raise-empty e)
  map-inv-compute-edge-graph-element-𝕎
    (tree-𝕎 a α) root-𝕎 (node-inclusion-graph-element-𝕎 (b , refl) y) e =
    ex-falso (is-empty-raise-empty e)
  map-inv-compute-edge-graph-element-𝕎
    (tree-𝕎 a α) (node-inclusion-graph-element-𝕎 (b , refl) x) root-𝕎 e =
    tr
      ( λ u → edge-graph-element-𝕎 (tree-𝕎 a α) u root-𝕎)
      ( inv
        ( ap (node-inclusion-graph-element-𝕎 (b , refl))
        ( is-injective-is-equiv
          ( is-equiv-map-compute-node-graph-element-𝕎 (α b)) e)))
      ( edge-to-root-graph-element-𝕎 (b , refl))
  map-inv-compute-edge-graph-element-𝕎
    ( tree-𝕎 a α)
    ( node-inclusion-graph-element-𝕎 (b , refl) m)
    ( node-inclusion-graph-element-𝕎 (.b , refl) n)
    ( refl , e) =
    edge-inclusion-graph-element-𝕎
      ( b , refl)
      ( map-inv-compute-edge-graph-element-𝕎 (α b) m n e)

--   map-inv-compute-edge-graph-element-𝕎 :
--     ( v : 𝕎 A B) (x y : node-graph-element-𝕎' v) →
--     edge-graph-element-𝕎' v x y →
--     edge-graph-element-𝕎 v
--       ( map-inv-compute-node-graph-element-𝕎 v x)
--       ( map-inv-compute-node-graph-element-𝕎 v y)
--   map-inv-compute-edge-graph-element-𝕎
--     (tree-𝕎 a α) (inl (b , m)) (inl (.b , n)) (refl , e) =
--     edge-inclusion-graph-element-𝕎
--       ( b , refl)
--       ( map-inv-compute-edge-graph-element-𝕎 (α b) m n e)
--   map-inv-compute-edge-graph-element-𝕎
--     (tree-𝕎 a α) (inl (b , .(root-𝕎' (α b)))) (inr star) refl =
--     tr
--       ( λ u → edge-graph-element-𝕎 (tree-𝕎 a α) u root-𝕎)
--       ( inv
--         ( isretr-map-inv-compute-node-graph-element-𝕎
--           ( tree-𝕎 a α)
--           ( node-inclusion-graph-element-𝕎 (b , refl) root-𝕎)))
--       ( edge-to-root-graph-element-𝕎 (b , refl))
--   map-inv-compute-edge-graph-element-𝕎
--     (tree-𝕎 a α) (inr star) (inl (c , n)) e =
--     ex-falso (is-empty-raise-empty e)
--   map-inv-compute-edge-graph-element-𝕎 (tree-𝕎 a α) (inr star) (inr star) e =
--     ex-falso (is-empty-raise-empty e)

--   issec-map-inv-compute-edge-graph-element-𝕎 :
--     (v : 𝕎 A B) (x y : node-graph-element-𝕎' v) →
--     ( {!map-compute-edge-graph-element-𝕎 v (map-inv-compute-node-graph-element-𝕎 v x) (map-inv-compute-node-graph-element-𝕎 v y)!} ∘ map-inv-compute-edge-graph-element-𝕎 v x y) ~ id
--   issec-map-inv-compute-edge-graph-element-𝕎 v x y = {!!}
-- ```

-- ### The type of edges from any node to the root is a proposition

-- ```agda
-- module _
--   {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
--   where

--   is-proof-irrelevant-edge-to-root-graph-element-𝕎 :
--     (w : 𝕎 A B) (x : node-graph-element-𝕎 w) →
--     is-proof-irrelevant (edge-graph-element-𝕎 w x root-𝕎)
--   is-proof-irrelevant-edge-to-root-graph-element-𝕎 w
--     .(node-inclusion-graph-element-𝕎 H root-𝕎)
--     (edge-to-root-graph-element-𝕎 H) =
--     is-contr-edge-to-root-graph-element-𝕎 H

--   is-prop-edge-to-root-graph-element-𝕎 :
--     (w : 𝕎 A B) (x : node-graph-element-𝕎 w) →
--     is-prop (edge-graph-element-𝕎 w x root-𝕎)
--   is-prop-edge-to-root-graph-element-𝕎 w x =
--     is-prop-is-proof-irrelevant
--       ( is-proof-irrelevant-edge-to-root-graph-element-𝕎 w x)
-- ```

-- -- ### The type of edges between any two nodes is a proposition

-- -- ```agda
-- -- module _
-- --   {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
-- --   where

-- --   is-proof-irrelevant-edge-graph-element-𝕎 :
-- --     (w : 𝕎 A B) (x y : node-graph-element-𝕎 w) →
-- --     is-proof-irrelevant (edge-graph-element-𝕎 w x y)
-- --   is-proof-irrelevant-edge-graph-element-𝕎 w ._ .root-𝕎
-- --     ( edge-to-root-graph-element-𝕎 H) =
-- --     is-contr-edge-to-root-graph-element-𝕎 H
-- --   is-proof-irrelevant-edge-graph-element-𝕎 w ._ ._
-- --     ( edge-inclusion-graph-element-𝕎 H e) =
-- --     {!!}

-- --   is-prop-edge-graph-element-𝕎 :
-- --     (w : 𝕎 A B) (x y : node-graph-element-𝕎 w) →
-- --     is-prop (edge-graph-element-𝕎 w x y)
-- --   is-prop-edge-graph-element-𝕎 w x y = {!!}
-- -- ```

-- -- ### The underlying graph of any element of a W-type is a directed tree

-- -- ```agda
-- -- module _
-- --   {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
-- --   where

-- --   walk-to-root-graph-element-𝕎 :
-- --     (w : 𝕎 A B) (x : node-graph-element-𝕎 w) →
-- --     walk-Graph (graph-element-𝕎 w) x root-𝕎
-- --   walk-to-root-graph-element-𝕎 w root-𝕎 = refl-walk-Graph
-- --   walk-to-root-graph-element-𝕎 w (node-inclusion-graph-element-𝕎 {v} H x) =
-- --     cons-walk-Graph
-- --       ( walk-hom-Graph
-- --         ( graph-element-𝕎 v)
-- --         ( graph-element-𝕎 w)
-- --         ( inclusion-graph-element-𝕎 H)
-- --         ( walk-to-root-graph-element-𝕎 v x))
-- --       ( edge-to-root-graph-element-𝕎 H)

-- --   is-trail-walk-to-root-graph-element-𝕎 :
-- --     (w : 𝕎 A B) (x : node-graph-element-𝕎 w) →
-- --     is-trail-walk-Graph
-- --       ( graph-element-𝕎 w)
-- --       ( walk-to-root-graph-element-𝕎 w x)
-- --   is-trail-walk-to-root-graph-element-𝕎 w x {(._ , .root-𝕎 , edge-to-root-graph-element-𝕎 H) , K} {.(node-inclusion-graph-element-𝕎 H root-𝕎 , root-𝕎 , edge-to-root-graph-element-𝕎 H) , K'} refl = {!!}
-- --   is-trail-walk-to-root-graph-element-𝕎 w x {(._ , ._ , edge-inclusion-graph-element-𝕎 H e) , K} {._ , K'} refl = {!!}

-- --   is-directed-tree-graph-element-𝕎 :
-- --     (w : 𝕎 A B) → is-directed-tree-Graph (graph-element-𝕎 w) root-𝕎
-- --   is-directed-tree-graph-element-𝕎 w x = {!!}
-- -- ```
