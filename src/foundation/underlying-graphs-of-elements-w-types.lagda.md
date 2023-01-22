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
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
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

### The map `node-inclusion-graph-element-𝕎 H` is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  contraction-fib-node-inclusion-graph-element-𝕎 :
    {u v : 𝕎 A B} (H : u ∈-𝕎 v) (x : node-graph-element-𝕎 v) →
    (y z : fib (node-inclusion-graph-element-𝕎 H) x) → y ＝ z
  contraction-fib-node-inclusion-graph-element-𝕎 H x (y , p) (z , q) = {!!}

  is-proof-irrelevant-fib-node-inclusion-graph-element-𝕎 :
    {u v : 𝕎 A B} (H : u ∈-𝕎 v) (x : node-graph-element-𝕎 v) →
    is-proof-irrelevant
      ( fib (node-inclusion-graph-element-𝕎 H) x)
  is-proof-irrelevant-fib-node-inclusion-graph-element-𝕎 H x (y , p) =
    {!!}

  is-prop-map-node-inclusion-graph-element-𝕎 :
    {u v : 𝕎 A B} (H : u ∈-𝕎 v) →
    is-prop-map (node-inclusion-graph-element-𝕎 {u = u} {v} H)
  is-prop-map-node-inclusion-graph-element-𝕎 {u} {v} H x =
    is-prop-is-proof-irrelevant
      ( λ { (y , refl) → {!!}})

  is-emb-node-inclusion-graph-element-𝕎 :
    {u v : 𝕎 A B} (H : u ∈-𝕎 v) →
    is-emb (node-inclusion-graph-element-𝕎 {u = u} {v} H)
  is-emb-node-inclusion-graph-element-𝕎 H = {!!}
```

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

### The type of edges from any node to the root is a proposition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-proof-irrelevant-edge-to-root-graph-element-𝕎 :
    (w : 𝕎 A B) (x : node-graph-element-𝕎 w) →
    is-proof-irrelevant (edge-graph-element-𝕎 w x root-𝕎)
  is-proof-irrelevant-edge-to-root-graph-element-𝕎 w
    .(node-inclusion-graph-element-𝕎 H root-𝕎)
    (edge-to-root-graph-element-𝕎 H) =
    is-contr-edge-to-root-graph-element-𝕎 H

  is-prop-edge-to-root-graph-element-𝕎 :
    (w : 𝕎 A B) (x : node-graph-element-𝕎 w) →
    is-prop (edge-graph-element-𝕎 w x root-𝕎)
  is-prop-edge-to-root-graph-element-𝕎 w x =
    is-prop-is-proof-irrelevant
      ( is-proof-irrelevant-edge-to-root-graph-element-𝕎 w x)
```

### The type of edges between any two nodes is a proposition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-proof-irrelevant-edge-graph-element-𝕎 :
    (w : 𝕎 A B) (x y : node-graph-element-𝕎 w) →
    is-proof-irrelevant (edge-graph-element-𝕎 w x y)
  is-proof-irrelevant-edge-graph-element-𝕎 w ._ .root-𝕎
    ( edge-to-root-graph-element-𝕎 H) =
    is-contr-edge-to-root-graph-element-𝕎 H
  is-proof-irrelevant-edge-graph-element-𝕎 w ._ ._
    ( edge-inclusion-graph-element-𝕎 H e) =
    {!!}

  is-prop-edge-graph-element-𝕎 :
    (w : 𝕎 A B) (x y : node-graph-element-𝕎 w) →
    is-prop (edge-graph-element-𝕎 w x y)
  is-prop-edge-graph-element-𝕎 w x y = {!!}
```

### The underlying graph of any element of a W-type is a directed tree

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  walk-to-root-graph-element-𝕎 :
    (w : 𝕎 A B) (x : node-graph-element-𝕎 w) →
    walk-Graph (graph-element-𝕎 w) x root-𝕎
  walk-to-root-graph-element-𝕎 w root-𝕎 = refl-walk-Graph
  walk-to-root-graph-element-𝕎 w (node-inclusion-graph-element-𝕎 {v} H x) =
    cons-walk-Graph
      ( walk-hom-Graph
        ( graph-element-𝕎 v)
        ( graph-element-𝕎 w)
        ( inclusion-graph-element-𝕎 H)
        ( walk-to-root-graph-element-𝕎 v x))
      ( edge-to-root-graph-element-𝕎 H)

  is-trail-walk-to-root-graph-element-𝕎 :
    (w : 𝕎 A B) (x : node-graph-element-𝕎 w) →
    is-trail-walk-Graph
      ( graph-element-𝕎 w)
      ( walk-to-root-graph-element-𝕎 w x)
  is-trail-walk-to-root-graph-element-𝕎 w x {(._ , .root-𝕎 , edge-to-root-graph-element-𝕎 H) , K} {.(node-inclusion-graph-element-𝕎 H root-𝕎 , root-𝕎 , edge-to-root-graph-element-𝕎 H) , K'} refl = {!!}
  is-trail-walk-to-root-graph-element-𝕎 w x {(._ , ._ , edge-inclusion-graph-element-𝕎 H e) , K} {._ , K'} refl = {!!}

  is-directed-tree-graph-element-𝕎 :
    (w : 𝕎 A B) → is-directed-tree-Graph (graph-element-𝕎 w) root-𝕎
  is-directed-tree-graph-element-𝕎 w x = {!!}
```

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
