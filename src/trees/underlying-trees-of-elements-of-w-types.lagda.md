# The underlying trees of elements of W-types

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module trees.underlying-trees-of-elements-of-w-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.isolated-points
open import foundation.negation
open import foundation.propositions
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.morphisms-directed-graphs
open import graph-theory.walks-directed-graphs

open import trees.combinator-directed-trees
open import trees.combinator-enriched-directed-trees
open import trees.directed-trees
open import trees.elementhood-relation-w-types
open import trees.enriched-directed-trees
open import trees.equivalences-directed-trees
open import trees.equivalences-enriched-directed-trees
open import trees.inequality-w-types
open import trees.w-types
```

</details>

## Idea

We assign to each element of a W-type `𝕎 A B` a directed graph. This directed
graph is in fact a directed tree, and furthermore, it can be given the structure
of an enriched directed tree. We show that the map from `𝕎 A B` to enriched
directed trees is an embedding.

## Definition

### The underlying graph of an element of a W-type

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  data node-element-𝕎 : 𝕎 A B → UU (l1 ⊔ l2) where
    root-𝕎 :
      {w : 𝕎 A B} → node-element-𝕎 w
    node-inclusion-element-𝕎 :
      {u v : 𝕎 A B} → (u ∈-𝕎 v) →
      node-element-𝕎 u → node-element-𝕎 v

  data edge-element-𝕎 :
    (w : 𝕎 A B) (x y : node-element-𝕎 w) → UU (l1 ⊔ l2)
    where
    edge-to-root-element-𝕎 :
      {u v : 𝕎 A B} (H : u ∈-𝕎 v) →
      edge-element-𝕎 v
        ( node-inclusion-element-𝕎 H root-𝕎)
        ( root-𝕎)
    edge-inclusion-element-𝕎 :
      {u v : 𝕎 A B} (H : u ∈-𝕎 v) →
      {x y : node-element-𝕎 u} (e : edge-element-𝕎 u x y) →
      edge-element-𝕎 v
        ( node-inclusion-element-𝕎 H x)
        ( node-inclusion-element-𝕎 H y)

  graph-element-𝕎 : 𝕎 A B → Directed-Graph (l1 ⊔ l2) (l1 ⊔ l2)
  pr1 (graph-element-𝕎 w) = node-element-𝕎 w
  pr2 (graph-element-𝕎 w) = edge-element-𝕎 w
```

### The external graph of an element of a W-type

```agda
  node-external-graph-element-𝕎 : 𝕎 A B → UU (l1 ⊔ l2)
  node-external-graph-element-𝕎 w = Σ (𝕎 A B) (λ u → u ≤-𝕎 w)

  edge-external-graph-element-𝕎 :
    (w : 𝕎 A B) (x y : node-external-graph-element-𝕎 w) → UU (l1 ⊔ l2)
  edge-external-graph-element-𝕎 w (x , H) (y , K) =
    Σ (x ∈-𝕎 y) (λ e → transitive-leq-𝕎 (leq-∈-𝕎 e) K ＝ H)

  external-graph-element-𝕎 : 𝕎 A B → Directed-Graph (l1 ⊔ l2) (l1 ⊔ l2)
  pr1 (external-graph-element-𝕎 w) = node-external-graph-element-𝕎 w
  pr2 (external-graph-element-𝕎 w) = edge-external-graph-element-𝕎 w
```

## Properties

### To be a root is decidable

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-root-node-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) → UU (l1 ⊔ l2)
  is-root-node-element-𝕎 w x = root-𝕎 ＝ x

  is-isolated-root-node-element-𝕎 :
    (w : 𝕎 A B) → is-isolated (root-𝕎 {w = w})
  is-isolated-root-node-element-𝕎 w root-𝕎 = inl refl
  is-isolated-root-node-element-𝕎 w
    ( node-inclusion-element-𝕎 H y) =
    inr (λ ())

  is-contr-loop-space-root-graph-element-𝕎 :
    (w : 𝕎 A B) → is-contr (root-𝕎 {w = w} ＝ root-𝕎)
  is-contr-loop-space-root-graph-element-𝕎 w =
    is-contr-loop-space-isolated-point root-𝕎
      ( is-isolated-root-node-element-𝕎 w)
```

### Characterization of equality of the type of nodes of the underlying graph of an element of `𝕎 A B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  data Eq-node-element-𝕎 (w : 𝕎 A B) :
    (x y : node-element-𝕎 w) → UU (l1 ⊔ l2)
    where
    root-refl-Eq-node-element-𝕎 :
      Eq-node-element-𝕎 w root-𝕎 root-𝕎
    node-inclusion-Eq-node-element-𝕎 :
      {u : 𝕎 A B} (H : u ∈-𝕎 w) {x y : node-element-𝕎 u} →
      Eq-node-element-𝕎 u x y →
      Eq-node-element-𝕎 w
        ( node-inclusion-element-𝕎 H x)
        ( node-inclusion-element-𝕎 H y)

  refl-Eq-node-element-𝕎 :
    {w : 𝕎 A B} (x : node-element-𝕎 w) →
    Eq-node-element-𝕎 w x x
  refl-Eq-node-element-𝕎 root-𝕎 = root-refl-Eq-node-element-𝕎
  refl-Eq-node-element-𝕎 (node-inclusion-element-𝕎 {u} H x) =
    node-inclusion-Eq-node-element-𝕎 H (refl-Eq-node-element-𝕎 x)

  center-total-Eq-node-element-𝕎 :
    {w : 𝕎 A B} (x : node-element-𝕎 w) →
    Σ (node-element-𝕎 w) (Eq-node-element-𝕎 w x)
  pr1 (center-total-Eq-node-element-𝕎 x) = x
  pr2 (center-total-Eq-node-element-𝕎 x) =
    refl-Eq-node-element-𝕎 x

  contraction-total-Eq-node-element-𝕎 :
    {w : 𝕎 A B} (x : node-element-𝕎 w) →
    (u : Σ (node-element-𝕎 w) (Eq-node-element-𝕎 w x)) →
    center-total-Eq-node-element-𝕎 x ＝ u
  contraction-total-Eq-node-element-𝕎 .root-𝕎
    (.root-𝕎 , root-refl-Eq-node-element-𝕎) =
    refl
  contraction-total-Eq-node-element-𝕎
    .(node-inclusion-element-𝕎 H _)
    ( .(node-inclusion-element-𝕎 H _) ,
      node-inclusion-Eq-node-element-𝕎 H e) =
    ap
      ( map-Σ
        ( λ z → Eq-node-element-𝕎 _ _ z)
        ( node-inclusion-element-𝕎 H)
        ( λ y → node-inclusion-Eq-node-element-𝕎 H))
      ( contraction-total-Eq-node-element-𝕎 _ (_ , e))

  is-contr-total-Eq-node-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    is-contr (Σ (node-element-𝕎 w) (Eq-node-element-𝕎 w x))
  pr1 (is-contr-total-Eq-node-element-𝕎 w x) =
    center-total-Eq-node-element-𝕎 x
  pr2 (is-contr-total-Eq-node-element-𝕎 w x) =
    contraction-total-Eq-node-element-𝕎 x

  Eq-eq-node-element-𝕎 :
    (w : 𝕎 A B) {x y : node-element-𝕎 w} →
    x ＝ y → Eq-node-element-𝕎 w x y
  Eq-eq-node-element-𝕎 w refl = refl-Eq-node-element-𝕎 _

  is-equiv-Eq-eq-node-element-𝕎 :
    (w : 𝕎 A B) (x y : node-element-𝕎 w) →
    is-equiv (Eq-eq-node-element-𝕎 w {x} {y})
  is-equiv-Eq-eq-node-element-𝕎 w x =
    fundamental-theorem-id
      ( is-contr-total-Eq-node-element-𝕎 w x)
      ( λ y → Eq-eq-node-element-𝕎 w {x} {y})

  extensionality-node-element-𝕎 :
    (w : 𝕎 A B) (x y : node-element-𝕎 w) →
    (x ＝ y) ≃ Eq-node-element-𝕎 w x y
  pr1 (extensionality-node-element-𝕎 w x y) =
    Eq-eq-node-element-𝕎 w {x} {y}
  pr2 (extensionality-node-element-𝕎 w x y) =
    is-equiv-Eq-eq-node-element-𝕎 w x y

  eq-Eq-node-element-𝕎 :
    (w : 𝕎 A B) (x y : node-element-𝕎 w) →
    Eq-node-element-𝕎 w x y → x ＝ y
  eq-Eq-node-element-𝕎 w x y =
    map-inv-equiv (extensionality-node-element-𝕎 w x y)
```

### The type of nodes of the underlying graph of an element of a W-type is a coproduct

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  node-element-𝕎' : 𝕎 A B → UU (l1 ⊔ l2)
  node-element-𝕎' (tree-𝕎 x α) =
    Σ (B x) (λ y → node-element-𝕎' (α y)) + unit

  map-compute-node-element-𝕎 :
    (w : 𝕎 A B) → node-element-𝕎 w → node-element-𝕎' w
  map-compute-node-element-𝕎 (tree-𝕎 x α) root-𝕎 = inr star
  map-compute-node-element-𝕎
    ( tree-𝕎 x α)
    ( node-inclusion-element-𝕎 (y , refl) n) =
    inl (pair y (map-compute-node-element-𝕎 (α y) n))

  map-inv-compute-node-element-𝕎 :
    (w : 𝕎 A B) → node-element-𝕎' w → node-element-𝕎 w
  map-inv-compute-node-element-𝕎 (tree-𝕎 x α) (inl (y , n)) =
    node-inclusion-element-𝕎
      ( pair y refl)
      ( map-inv-compute-node-element-𝕎 (α y) n)
  map-inv-compute-node-element-𝕎 (tree-𝕎 x α) (inr star) = root-𝕎

  issec-map-inv-compute-node-element-𝕎 :
    (w : 𝕎 A B) →
    ( map-compute-node-element-𝕎 w ∘
      map-inv-compute-node-element-𝕎 w) ~ id
  issec-map-inv-compute-node-element-𝕎 (tree-𝕎 x α) (inl (y , n)) =
    ap
      ( inl)
      ( eq-pair-Σ refl (issec-map-inv-compute-node-element-𝕎 (α y) n))
  issec-map-inv-compute-node-element-𝕎 (tree-𝕎 x α) (inr star) = refl

  isretr-map-inv-compute-node-element-𝕎 :
    (w : 𝕎 A B) →
    ( map-inv-compute-node-element-𝕎 w ∘
      map-compute-node-element-𝕎 w) ~ id
  isretr-map-inv-compute-node-element-𝕎 (tree-𝕎 x α) root-𝕎 = refl
  isretr-map-inv-compute-node-element-𝕎
    ( tree-𝕎 x α)
    ( node-inclusion-element-𝕎 (y , refl) n) =
    ap
      ( node-inclusion-element-𝕎 (y , refl))
      ( isretr-map-inv-compute-node-element-𝕎 (α y) n)

  is-equiv-map-compute-node-element-𝕎 :
    (w : 𝕎 A B) → is-equiv (map-compute-node-element-𝕎 w)
  is-equiv-map-compute-node-element-𝕎 w =
    is-equiv-has-inverse
      ( map-inv-compute-node-element-𝕎 w)
      ( issec-map-inv-compute-node-element-𝕎 w)
      ( isretr-map-inv-compute-node-element-𝕎 w)

  compute-node-element-𝕎 :
    (w : 𝕎 A B) → node-element-𝕎 w ≃ node-element-𝕎' w
  pr1 (compute-node-element-𝕎 w) = map-compute-node-element-𝕎 w
  pr2 (compute-node-element-𝕎 w) =
    is-equiv-map-compute-node-element-𝕎 w
```

### The node-inclusion on the coproduct representation of the type of nodes

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  node-inclusion-element-𝕎' :
    (v : 𝕎 A B) (y : B (symbol-𝕎 v)) →
    node-element-𝕎' (component-𝕎 v y) → node-element-𝕎' v
  node-inclusion-element-𝕎' (tree-𝕎 x α) y n = inl (pair y n)
```

Note that we don't expect that `node-inclusion-element-𝕎'` is an embedding. The
total space `Σ (y : B x), node-element-𝕎' (α y)` embeds into
`node-element-𝕎' (tree-𝕎 x α)`, and this implies that the node inclusion has the
same truncation level as the fiber inclusions

```md
  node-element-𝕎' (α b) → Σ (y : B x), node-element-𝕎' (α y)
```

In other words, the fiber is `Ω (B , b)`.

### For any `u ∈-𝕎 v` in `𝕎 A B` we have a graph inclusion from the underlying graph of `u` to the underlying graph of `v`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  inclusion-graph-element-𝕎 :
    {u v : 𝕎 A B} → u ∈-𝕎 v →
    hom-Directed-Graph (graph-element-𝕎 u) (graph-element-𝕎 v)
  pr1 (inclusion-graph-element-𝕎 {u} {v} H) =
    node-inclusion-element-𝕎 H
  pr2 (inclusion-graph-element-𝕎 {u} {v} H) x y e =
    edge-inclusion-element-𝕎 H e
```

### The type of edges from the root of `u ∈-𝕎 v` to the root of `v` is contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-contr-edge-to-root-element-𝕎 :
    {u v : 𝕎 A B} (H : u ∈-𝕎 v) →
    is-contr
      ( edge-element-𝕎 v
        ( node-inclusion-element-𝕎 H root-𝕎)
        ( root-𝕎))
  pr1 (is-contr-edge-to-root-element-𝕎 H) =
    edge-to-root-element-𝕎 H
  pr2
    ( is-contr-edge-to-root-element-𝕎 H)
    ( edge-to-root-element-𝕎 .H) =
    refl
```

### Computing the type of edges between nodes

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  root-𝕎' : (w : 𝕎 A B) → node-element-𝕎' w
  root-𝕎' w = map-compute-node-element-𝕎 w root-𝕎

  edge-element-𝕎' :
    (v : 𝕎 A B) (x y : node-element-𝕎' v) → UU (l1 ⊔ l2)
  edge-element-𝕎' (tree-𝕎 a α) (inl (y , m)) (inl (z , n)) =
    Σ ( y ＝ z)
      ( λ p →
        edge-element-𝕎' (α z) (tr node-element-𝕎' (ap α p) m) n)
  edge-element-𝕎' (tree-𝕎 a α) (inl (x , n)) (inr star) =
    n ＝ root-𝕎' (α x)
  edge-element-𝕎' (tree-𝕎 a α) (inr star) (inl y) =
    raise-empty (l1 ⊔ l2)
  edge-element-𝕎' (tree-𝕎 a α) (inr star) (inr star) =
    raise-empty (l1 ⊔ l2)

  root-map-compute-node-element-𝕎 :
    (w : 𝕎 A B) →
    map-compute-node-element-𝕎 w root-𝕎 ＝ root-𝕎' w
  root-map-compute-node-element-𝕎 (tree-𝕎 a α) = refl

  map-compute-edge-element-𝕎 :
    (v : 𝕎 A B) (x y : node-element-𝕎 v) →
    edge-element-𝕎 v x y →
    edge-element-𝕎' v
      ( map-compute-node-element-𝕎 v x)
      ( map-compute-node-element-𝕎 v y)
  map-compute-edge-element-𝕎
    ( tree-𝕎 a α)
    .( node-inclusion-element-𝕎 (b , refl) root-𝕎)
    .( root-𝕎)
    ( edge-to-root-element-𝕎 (b , refl)) =
    refl
  map-compute-edge-element-𝕎
    ( tree-𝕎 x α)
    .( node-inclusion-element-𝕎 (b , refl) _)
    .( node-inclusion-element-𝕎 (b , refl) _)
    ( edge-inclusion-element-𝕎 (b , refl) {m} {n} e) =
    (refl , map-compute-edge-element-𝕎 (α b) m n e)

  map-inv-compute-edge-element-𝕎 :
    ( v : 𝕎 A B) (x y : node-element-𝕎 v) →
    edge-element-𝕎' v
      ( map-compute-node-element-𝕎 v x)
      ( map-compute-node-element-𝕎 v y) →
    edge-element-𝕎 v x y
  map-inv-compute-edge-element-𝕎 (tree-𝕎 a α) root-𝕎 root-𝕎 e =
    ex-falso (is-empty-raise-empty e)
  map-inv-compute-edge-element-𝕎
    (tree-𝕎 a α) root-𝕎 (node-inclusion-element-𝕎 (b , refl) y) e =
    ex-falso (is-empty-raise-empty e)
  map-inv-compute-edge-element-𝕎
    (tree-𝕎 a α) (node-inclusion-element-𝕎 (b , refl) x) root-𝕎 e =
    tr
      ( λ u → edge-element-𝕎 (tree-𝕎 a α) u root-𝕎)
      ( inv
        ( ap (node-inclusion-element-𝕎 (b , refl))
        ( is-injective-is-equiv
          ( is-equiv-map-compute-node-element-𝕎 (α b)) e)))
      ( edge-to-root-element-𝕎 (b , refl))
  map-inv-compute-edge-element-𝕎
    ( tree-𝕎 a α)
    ( node-inclusion-element-𝕎 (b , refl) m)
    ( node-inclusion-element-𝕎 (.b , refl) n)
    ( refl , e) =
    edge-inclusion-element-𝕎
      ( b , refl)
      ( map-inv-compute-edge-element-𝕎 (α b) m n e)
```

### The type of edges from any node to the root is a proposition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-proof-irrelevant-edge-to-root-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    is-proof-irrelevant (edge-element-𝕎 w x root-𝕎)
  is-proof-irrelevant-edge-to-root-element-𝕎 w
    .(node-inclusion-element-𝕎 H root-𝕎)
    (edge-to-root-element-𝕎 H) =
    is-contr-edge-to-root-element-𝕎 H

  is-prop-edge-to-root-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    is-prop (edge-element-𝕎 w x root-𝕎)
  is-prop-edge-to-root-element-𝕎 w x =
    is-prop-is-proof-irrelevant
      ( is-proof-irrelevant-edge-to-root-element-𝕎 w x)
```

### The underlying graph of any element of a W-type is a directed tree

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  no-edge-from-root-graph-element-𝕎 :
    (w : 𝕎 A B) →
    is-empty (Σ (node-element-𝕎 w) (edge-element-𝕎 w root-𝕎))
  no-edge-from-root-graph-element-𝕎 w (x , ())

  is-empty-eq-root-node-inclusion-element-𝕎 :
    {v w : 𝕎 A B} (H : v ∈-𝕎 w) (x : node-element-𝕎 v) →
    ¬ (root-𝕎 {w = w} ＝ node-inclusion-element-𝕎 H x)
  is-empty-eq-root-node-inclusion-element-𝕎 H x ()

  has-unique-predecessor-node-inclusion-element-𝕎 :
    {v w : 𝕎 A B} (H : v ∈-𝕎 w) (x : node-element-𝕎 v) →
    is-contr
      ( Σ ( node-element-𝕎 w)
          ( edge-element-𝕎 w (node-inclusion-element-𝕎 H x)))
  pr1 (pr1 (has-unique-predecessor-node-inclusion-element-𝕎 H root-𝕎)) =
    root-𝕎
  pr2 (pr1 (has-unique-predecessor-node-inclusion-element-𝕎 H root-𝕎)) =
    edge-to-root-element-𝕎 H
  pr2
    ( has-unique-predecessor-node-inclusion-element-𝕎 H root-𝕎)
    ( .root-𝕎 , edge-to-root-element-𝕎 .H) =
    refl
  pr1
    ( has-unique-predecessor-node-inclusion-element-𝕎 H
      ( node-inclusion-element-𝕎 K x)) =
    map-Σ
      ( λ y →
        edge-element-𝕎 _
          ( node-inclusion-element-𝕎 H
            ( node-inclusion-element-𝕎 K x))
          ( y))
      ( node-inclusion-element-𝕎 H)
      ( λ y → edge-inclusion-element-𝕎 H)
      ( center (has-unique-predecessor-node-inclusion-element-𝕎 K x))
  pr2
    ( has-unique-predecessor-node-inclusion-element-𝕎 H
      ( node-inclusion-element-𝕎 K x))
    ( .(node-inclusion-element-𝕎 H _) ,
      edge-inclusion-element-𝕎 .H f) =
    ap
      ( map-Σ _
        ( node-inclusion-element-𝕎 H)
        ( λ y → edge-inclusion-element-𝕎 H))
      ( eq-is-contr
        ( has-unique-predecessor-node-inclusion-element-𝕎 K x))

  has-unique-predecessor-graph-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    is-contr
      ((root-𝕎 ＝ x) + Σ (node-element-𝕎 w) (edge-element-𝕎 w x))
  has-unique-predecessor-graph-element-𝕎 w root-𝕎 =
    is-contr-equiv
      ( root-𝕎 ＝ root-𝕎)
      ( right-unit-law-coprod-is-empty
        ( root-𝕎 ＝ root-𝕎)
        ( Σ (node-element-𝕎 w) (edge-element-𝕎 w root-𝕎))
        ( no-edge-from-root-graph-element-𝕎 w))
      ( is-contr-loop-space-root-graph-element-𝕎 w)
  has-unique-predecessor-graph-element-𝕎 w
    ( node-inclusion-element-𝕎 H x) =
    is-contr-equiv
      ( Σ ( node-element-𝕎 w)
          ( edge-element-𝕎 w (node-inclusion-element-𝕎 H x)))
      ( left-unit-law-coprod-is-empty
        ( root-𝕎 ＝ node-inclusion-element-𝕎 H x)
        ( Σ ( node-element-𝕎 w)
            ( edge-element-𝕎 w (node-inclusion-element-𝕎 H x)))
        ( is-empty-eq-root-node-inclusion-element-𝕎 H x))
      ( has-unique-predecessor-node-inclusion-element-𝕎 H x)

  walk-to-root-graph-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    walk-Directed-Graph (graph-element-𝕎 w) x root-𝕎
  walk-to-root-graph-element-𝕎 w root-𝕎 = refl-walk-Directed-Graph
  walk-to-root-graph-element-𝕎 w (node-inclusion-element-𝕎 {v} H x) =
    snoc-walk-Directed-Graph
      ( graph-element-𝕎 w)
      ( walk-hom-Directed-Graph
        ( graph-element-𝕎 v)
        ( graph-element-𝕎 w)
        ( inclusion-graph-element-𝕎 H)
        ( walk-to-root-graph-element-𝕎 v x))
      ( edge-to-root-element-𝕎 H)

  is-tree-graph-element-𝕎 :
    (w : 𝕎 A B) → is-tree-Directed-Graph' (graph-element-𝕎 w) root-𝕎
  is-tree-graph-element-𝕎 w =
    is-tree-unique-parent-Directed-Graph'
      ( graph-element-𝕎 w)
      ( root-𝕎)
      ( has-unique-predecessor-graph-element-𝕎 w)
      ( walk-to-root-graph-element-𝕎 w)

  directed-tree-element-𝕎 :
    𝕎 A B → Directed-Tree (l1 ⊔ l2) (l1 ⊔ l2)
  pr1 (directed-tree-element-𝕎 w) = graph-element-𝕎 w
  pr1 (pr2 (directed-tree-element-𝕎 w)) = root-𝕎
  pr2 (pr2 (directed-tree-element-𝕎 w)) = is-tree-graph-element-𝕎 w
```

### The external graph of an element of a W-type is equivalent to the underlying graph

### The underlying graph of an element of a W-type can be given the structure of an enriched directed tree

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  shape-node-directed-tree-element-𝕎 :
    (w : 𝕎 A B) → node-element-𝕎 w → A
  shape-node-directed-tree-element-𝕎 w root-𝕎 = symbol-𝕎 w
  shape-node-directed-tree-element-𝕎 w
    ( node-inclusion-element-𝕎 {u} H y) =
    shape-node-directed-tree-element-𝕎 u y

  map-enrichment-directed-tree-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    B (shape-node-directed-tree-element-𝕎 w x) →
    Σ (node-element-𝕎 w) (λ y → edge-element-𝕎 w y x)
  pr1 (map-enrichment-directed-tree-element-𝕎 w root-𝕎 b) =
    node-inclusion-element-𝕎 (b , refl) root-𝕎
  pr2 (map-enrichment-directed-tree-element-𝕎 w root-𝕎 b) =
    edge-to-root-element-𝕎 (b , refl)
  map-enrichment-directed-tree-element-𝕎 w
    ( node-inclusion-element-𝕎 {u} H y) b =
    map-Σ
      ( λ z →
        edge-element-𝕎 w z (node-inclusion-element-𝕎 H y))
      ( node-inclusion-element-𝕎 H)
      ( λ z → edge-inclusion-element-𝕎 H)
      ( map-enrichment-directed-tree-element-𝕎 u y b)

  map-inv-enrichment-directed-tree-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    Σ (node-element-𝕎 w) (λ y → edge-element-𝕎 w y x) →
    B (shape-node-directed-tree-element-𝕎 w x)
  map-inv-enrichment-directed-tree-element-𝕎 w .root-𝕎
    ( ._ , edge-to-root-element-𝕎 H) = pr1 H
  map-inv-enrichment-directed-tree-element-𝕎 w ._
    ( ._ , edge-inclusion-element-𝕎 {u} H {x} {y} e) =
    map-inv-enrichment-directed-tree-element-𝕎 u y (x , e)

  issec-map-inv-enrichment-directed-tree-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    ( map-enrichment-directed-tree-element-𝕎 w x ∘
      map-inv-enrichment-directed-tree-element-𝕎 w x) ~ id
  issec-map-inv-enrichment-directed-tree-element-𝕎 w .root-𝕎
    ( ._ , edge-to-root-element-𝕎 (b , refl)) = refl
  issec-map-inv-enrichment-directed-tree-element-𝕎 w ._
    ( ._ , edge-inclusion-element-𝕎 {u} H {x} {y} e) =
    ap
      ( map-Σ
        ( λ z →
          edge-element-𝕎 w z (node-inclusion-element-𝕎 H y))
        ( node-inclusion-element-𝕎 H)
        ( λ z → edge-inclusion-element-𝕎 H))
      ( issec-map-inv-enrichment-directed-tree-element-𝕎 u y (x , e))

  isretr-map-inv-enrichment-directed-tree-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    ( map-inv-enrichment-directed-tree-element-𝕎 w x ∘
      map-enrichment-directed-tree-element-𝕎 w x) ~ id
  isretr-map-inv-enrichment-directed-tree-element-𝕎 w root-𝕎 b = refl
  isretr-map-inv-enrichment-directed-tree-element-𝕎 w
    ( node-inclusion-element-𝕎 {u} H y) b =
    isretr-map-inv-enrichment-directed-tree-element-𝕎 u y b

  is-equiv-map-enrichment-directed-tree-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    is-equiv (map-enrichment-directed-tree-element-𝕎 w x)
  is-equiv-map-enrichment-directed-tree-element-𝕎 w x =
    is-equiv-has-inverse
      ( map-inv-enrichment-directed-tree-element-𝕎 w x)
      ( issec-map-inv-enrichment-directed-tree-element-𝕎 w x)
      ( isretr-map-inv-enrichment-directed-tree-element-𝕎 w x)

  enrichment-directed-tree-element-𝕎 :
    (w : 𝕎 A B) (x : node-element-𝕎 w) →
    B (shape-node-directed-tree-element-𝕎 w x) ≃
    Σ (node-element-𝕎 w) (λ y → edge-element-𝕎 w y x)
  pr1 (enrichment-directed-tree-element-𝕎 w x) =
    map-enrichment-directed-tree-element-𝕎 w x
  pr2 (enrichment-directed-tree-element-𝕎 w x) =
    is-equiv-map-enrichment-directed-tree-element-𝕎 w x

  enriched-directed-tree-element-𝕎 :
    𝕎 A B → Enriched-Directed-Tree (l1 ⊔ l2) (l1 ⊔ l2) A B
  pr1 (enriched-directed-tree-element-𝕎 w) = directed-tree-element-𝕎 w
  pr1 (pr2 (enriched-directed-tree-element-𝕎 w)) =
    shape-node-directed-tree-element-𝕎 w
  pr2 (pr2 (enriched-directed-tree-element-𝕎 w)) =
    enrichment-directed-tree-element-𝕎 w
```

### The underlying tree of `tree-𝕎 a α` is the combinator tree of the underlying trees of `α b` indexed by `b : B a`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (w : 𝕎 A B)
  where

  node-compute-directed-tree-element-𝕎 :
    node-element-𝕎 w →
    node-combinator-Directed-Tree
      ( λ b → directed-tree-element-𝕎 (component-𝕎 w b))
  node-compute-directed-tree-element-𝕎 root-𝕎 =
    root-combinator-Directed-Tree
  node-compute-directed-tree-element-𝕎
    ( node-inclusion-element-𝕎 (b , refl) x) =
    node-inclusion-combinator-Directed-Tree b x

  map-inv-node-compute-directed-tree-element-𝕎 :
    node-combinator-Directed-Tree
      ( λ b → directed-tree-element-𝕎 (component-𝕎 w b)) →
    node-element-𝕎 w
  map-inv-node-compute-directed-tree-element-𝕎
    root-combinator-Directed-Tree =
    root-𝕎
  map-inv-node-compute-directed-tree-element-𝕎
    ( node-inclusion-combinator-Directed-Tree b x) =
    node-inclusion-element-𝕎 (b , refl) x

  issec-map-inv-node-compute-directed-tree-element-𝕎 :
    ( node-compute-directed-tree-element-𝕎 ∘
      map-inv-node-compute-directed-tree-element-𝕎) ~ id
  issec-map-inv-node-compute-directed-tree-element-𝕎
    root-combinator-Directed-Tree =
    refl
  issec-map-inv-node-compute-directed-tree-element-𝕎
    ( node-inclusion-combinator-Directed-Tree i x) =
    refl

  isretr-map-inv-node-compute-directed-tree-element-𝕎 :
    ( map-inv-node-compute-directed-tree-element-𝕎 ∘
      node-compute-directed-tree-element-𝕎) ~ id
  isretr-map-inv-node-compute-directed-tree-element-𝕎 root-𝕎 = refl
  isretr-map-inv-node-compute-directed-tree-element-𝕎
    ( node-inclusion-element-𝕎 (b , refl) x) =
    refl

  is-equiv-node-compute-directed-tree-element-𝕎 :
    is-equiv node-compute-directed-tree-element-𝕎
  is-equiv-node-compute-directed-tree-element-𝕎 =
    is-equiv-has-inverse
      map-inv-node-compute-directed-tree-element-𝕎
      issec-map-inv-node-compute-directed-tree-element-𝕎
      isretr-map-inv-node-compute-directed-tree-element-𝕎

  equiv-node-compute-directed-tree-element-𝕎 :
    node-element-𝕎 w ≃
    node-combinator-Directed-Tree
      ( λ b → directed-tree-element-𝕎 (component-𝕎 w b))
  pr1 equiv-node-compute-directed-tree-element-𝕎 =
    node-compute-directed-tree-element-𝕎
  pr2 equiv-node-compute-directed-tree-element-𝕎 =
    is-equiv-node-compute-directed-tree-element-𝕎

  edge-compute-directed-tree-element-𝕎 :
    (x y : node-element-𝕎 w) →
    edge-element-𝕎 w x y →
    edge-combinator-Directed-Tree
      ( λ b → directed-tree-element-𝕎 (component-𝕎 w b))
      ( node-compute-directed-tree-element-𝕎 x)
      ( node-compute-directed-tree-element-𝕎 y)
  edge-compute-directed-tree-element-𝕎 ._ .root-𝕎
    ( edge-to-root-element-𝕎 (b , refl)) =
    edge-to-root-combinator-Directed-Tree b
  edge-compute-directed-tree-element-𝕎 ._ ._
    ( edge-inclusion-element-𝕎 (b , refl) e) =
    edge-inclusion-combinator-Directed-Tree b _ _ e

  map-inv-edge-compute-directed-tree-element-𝕎' :
    ( x y :
      node-combinator-Directed-Tree
        ( directed-tree-element-𝕎 ∘ component-𝕎 w)) →
    edge-combinator-Directed-Tree
      ( λ b → directed-tree-element-𝕎 (component-𝕎 w b))
      ( x)
      ( y) →
    edge-element-𝕎 w
      ( map-inv-node-compute-directed-tree-element-𝕎 x)
      ( map-inv-node-compute-directed-tree-element-𝕎 y)
  map-inv-edge-compute-directed-tree-element-𝕎' ._ ._
    ( edge-to-root-combinator-Directed-Tree b) =
    edge-to-root-element-𝕎 (b , refl)
  map-inv-edge-compute-directed-tree-element-𝕎' ._ ._
    ( edge-inclusion-combinator-Directed-Tree b x y e) =
    edge-inclusion-element-𝕎 (b , refl) e

  map-inv-edge-compute-directed-tree-element-𝕎 :
    ( x y : node-element-𝕎 w) →
    edge-combinator-Directed-Tree
      ( λ b → directed-tree-element-𝕎 (component-𝕎 w b))
      ( node-compute-directed-tree-element-𝕎 x)
      ( node-compute-directed-tree-element-𝕎 y) →
    edge-element-𝕎 w x y
  map-inv-edge-compute-directed-tree-element-𝕎 x y =
    ( binary-tr
      ( edge-element-𝕎 w)
      ( isretr-map-inv-node-compute-directed-tree-element-𝕎 x)
      ( isretr-map-inv-node-compute-directed-tree-element-𝕎 y)) ∘
    ( map-inv-edge-compute-directed-tree-element-𝕎'
      ( node-compute-directed-tree-element-𝕎 x)
      ( node-compute-directed-tree-element-𝕎 y))

  issec-map-inv-edge-compute-directed-tree-element-𝕎' :
    ( x y :
      node-combinator-Directed-Tree
        ( directed-tree-element-𝕎 ∘ component-𝕎 w)) →
    ( e :
      edge-combinator-Directed-Tree
        ( λ b → directed-tree-element-𝕎 (component-𝕎 w b))
        ( x)
        ( y)) →
    binary-tr
      ( edge-combinator-Directed-Tree
        ( λ b → directed-tree-element-𝕎 (component-𝕎 w b)))
      ( issec-map-inv-node-compute-directed-tree-element-𝕎 x)
      ( issec-map-inv-node-compute-directed-tree-element-𝕎 y)
      ( edge-compute-directed-tree-element-𝕎
        ( map-inv-node-compute-directed-tree-element-𝕎 x)
        ( map-inv-node-compute-directed-tree-element-𝕎 y)
        ( map-inv-edge-compute-directed-tree-element-𝕎' x y e)) ＝ e
  issec-map-inv-edge-compute-directed-tree-element-𝕎' ._ ._
    ( edge-to-root-combinator-Directed-Tree i) =
    refl
  issec-map-inv-edge-compute-directed-tree-element-𝕎' ._ ._
    ( edge-inclusion-combinator-Directed-Tree i x y e) =
    refl

  issec-map-inv-edge-compute-directed-tree-element-𝕎 :
    (x y : node-element-𝕎 w) →
    ( e :
      edge-combinator-Directed-Tree
        ( λ b → directed-tree-element-𝕎 (component-𝕎 w b))
        ( node-compute-directed-tree-element-𝕎 x)
        ( node-compute-directed-tree-element-𝕎 y)) →
    edge-compute-directed-tree-element-𝕎 x y
      ( map-inv-edge-compute-directed-tree-element-𝕎 x y e) ＝ e
  issec-map-inv-edge-compute-directed-tree-element-𝕎
    ( node-inclusion-element-𝕎 (b , refl) x) root-𝕎 e =
    issec-map-inv-edge-compute-directed-tree-element-𝕎'
      ( node-compute-directed-tree-element-𝕎 _)
      ( node-compute-directed-tree-element-𝕎 _)
      ( e)
  issec-map-inv-edge-compute-directed-tree-element-𝕎
    ( node-inclusion-element-𝕎 (b , refl) x)
    ( node-inclusion-element-𝕎 (c , refl) y)
    ( e) =
    issec-map-inv-edge-compute-directed-tree-element-𝕎'
      ( node-compute-directed-tree-element-𝕎 _)
      ( node-compute-directed-tree-element-𝕎 _)
      ( e)

  isretr-map-inv-edge-compute-directed-tree-element-𝕎 :
    (x y : node-element-𝕎 w) (e : edge-element-𝕎 w x y) →
    map-inv-edge-compute-directed-tree-element-𝕎 x y
      ( edge-compute-directed-tree-element-𝕎 x y e) ＝ e
  isretr-map-inv-edge-compute-directed-tree-element-𝕎 ._ .root-𝕎
    ( edge-to-root-element-𝕎 (b , refl)) = refl
  isretr-map-inv-edge-compute-directed-tree-element-𝕎 ._ ._
    ( edge-inclusion-element-𝕎 (b , refl) e) = refl

  is-equiv-edge-compute-directed-tree-element-𝕎 :
    (x y : node-element-𝕎 w) →
    is-equiv (edge-compute-directed-tree-element-𝕎 x y)
  is-equiv-edge-compute-directed-tree-element-𝕎 x y =
    is-equiv-has-inverse
      ( map-inv-edge-compute-directed-tree-element-𝕎 x y)
      ( issec-map-inv-edge-compute-directed-tree-element-𝕎 x y)
      ( isretr-map-inv-edge-compute-directed-tree-element-𝕎 x y)

  equiv-edge-compute-directed-tree-element-𝕎 :
    (x y : node-element-𝕎 w) →
    edge-element-𝕎 w x y ≃
    edge-combinator-Directed-Tree
      ( λ b → directed-tree-element-𝕎 (component-𝕎 w b))
      ( node-compute-directed-tree-element-𝕎 x)
      ( node-compute-directed-tree-element-𝕎 y)
  pr1 (equiv-edge-compute-directed-tree-element-𝕎 x y) =
    edge-compute-directed-tree-element-𝕎 x y
  pr2 (equiv-edge-compute-directed-tree-element-𝕎 x y) =
    is-equiv-edge-compute-directed-tree-element-𝕎 x y

  compute-directed-tree-element-𝕎 :
    equiv-Directed-Tree
      ( directed-tree-element-𝕎 w)
      ( combinator-Directed-Tree
        ( λ b → directed-tree-element-𝕎 (component-𝕎 w b)))
  pr1 compute-directed-tree-element-𝕎 =
    equiv-node-compute-directed-tree-element-𝕎
  pr2 compute-directed-tree-element-𝕎 =
    equiv-edge-compute-directed-tree-element-𝕎

  shape-compute-enriched-directed-tree-element-𝕎 :
    shape-node-directed-tree-element-𝕎 w ~
    ( ( shape-combinator-Enriched-Directed-Tree A B
        ( symbol-𝕎 w)
        ( λ b → enriched-directed-tree-element-𝕎 (component-𝕎 w b))) ∘
      ( node-compute-directed-tree-element-𝕎))
  shape-compute-enriched-directed-tree-element-𝕎 root-𝕎 = refl
  shape-compute-enriched-directed-tree-element-𝕎
    ( node-inclusion-element-𝕎 (b , refl) x) =
    refl

  enrichment-compute-enriched-directed-tree-element-𝕎 :
    (x : node-element-𝕎 w) →
    htpy-equiv
      ( ( equiv-children-equiv-Directed-Tree
          ( directed-tree-element-𝕎 w)
          ( combinator-Directed-Tree
            ( λ b → directed-tree-element-𝕎 (component-𝕎 w b)))
          ( compute-directed-tree-element-𝕎)
          ( x)) ∘e
        ( enrichment-directed-tree-element-𝕎 w x))
      ( ( enrichment-combinator-Enriched-Directed-Tree A B
          ( symbol-𝕎 w)
          ( λ b → enriched-directed-tree-element-𝕎 (component-𝕎 w b))
          ( node-compute-directed-tree-element-𝕎 x)) ∘e
        ( equiv-tr B
          ( shape-compute-enriched-directed-tree-element-𝕎 x)))
  enrichment-compute-enriched-directed-tree-element-𝕎 root-𝕎 b = refl
  enrichment-compute-enriched-directed-tree-element-𝕎
    ( node-inclusion-element-𝕎 (c , refl) x) b =
    refl

  compute-enriched-directed-tree-element-𝕎 :
    equiv-Enriched-Directed-Tree A B
      ( enriched-directed-tree-element-𝕎 w)
      ( combinator-Enriched-Directed-Tree A B
        ( symbol-𝕎 w)
        ( λ b → enriched-directed-tree-element-𝕎 (component-𝕎 w b)))
  pr1 compute-enriched-directed-tree-element-𝕎 =
    compute-directed-tree-element-𝕎
  pr1 (pr2 compute-enriched-directed-tree-element-𝕎) =
    shape-compute-enriched-directed-tree-element-𝕎
  pr2 (pr2 compute-enriched-directed-tree-element-𝕎) =
    enrichment-compute-enriched-directed-tree-element-𝕎
```

### The map `enriched-directed-tree-element-𝕎` is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  center-is-proof-irrelevant-fib-enriched-directed-tree-element-𝕎 :
    (w : 𝕎 A B) →
    Σ ( 𝕎 A B)
      ( λ v →
        equiv-Enriched-Directed-Tree A B
          ( enriched-directed-tree-element-𝕎 v)
          ( enriched-directed-tree-element-𝕎 w))
  pr1 (center-is-proof-irrelevant-fib-enriched-directed-tree-element-𝕎 w )= w
  pr2 (center-is-proof-irrelevant-fib-enriched-directed-tree-element-𝕎 w )=
    id-equiv-Enriched-Directed-Tree A B
      ( enriched-directed-tree-element-𝕎 w)

  eq-symbol-equiv-enriched-directed-tree-element-𝕎 :
    (v w : 𝕎 A B) →
    equiv-Enriched-Directed-Tree A B
      ( enriched-directed-tree-element-𝕎 v)
      ( enriched-directed-tree-element-𝕎 w) →
    symbol-𝕎 v ＝ symbol-𝕎 w
  eq-symbol-equiv-enriched-directed-tree-element-𝕎 v w e =
    ( shape-equiv-Enriched-Directed-Tree A B
      ( enriched-directed-tree-element-𝕎 v)
      ( enriched-directed-tree-element-𝕎 w)
      ( e)
      ( root-𝕎)) ∙
    ( ap
      ( shape-node-directed-tree-element-𝕎 w)
      ( preserves-root-equiv-Enriched-Directed-Tree A B
        ( enriched-directed-tree-element-𝕎 v)
        ( enriched-directed-tree-element-𝕎 w)
        ( e)))

  htpy-component-equiv-enriched-directed-tree-element-𝕎 :
    (v w : 𝕎 A B) →
    ( e :
      equiv-Enriched-Directed-Tree A B
        ( enriched-directed-tree-element-𝕎 v)
        ( enriched-directed-tree-element-𝕎 w)) →
    component-𝕎 v ~
    ( component-𝕎 w ∘
      tr B (eq-symbol-equiv-enriched-directed-tree-element-𝕎 v w e))
  htpy-component-equiv-enriched-directed-tree-element-𝕎 v w e = {!!}

  base-contraction-is-proof-irrelevant-fib-enriched-directed-tree-element-𝕎 :
    (w : 𝕎 A B) →
    ( x :
      Σ ( 𝕎 A B)
        ( λ v →
          equiv-Enriched-Directed-Tree A B
            ( enriched-directed-tree-element-𝕎 v)
            ( enriched-directed-tree-element-𝕎 w))) →
    w ＝ pr1 x
  base-contraction-is-proof-irrelevant-fib-enriched-directed-tree-element-𝕎
    (tree-𝕎 a α)
    (tree-𝕎 b β , e) =
    eq-Eq-𝕎
      ( tree-𝕎 a α)
      ( tree-𝕎 b β)
      ( eq-symbol-equiv-enriched-directed-tree-element-𝕎
        ( tree-𝕎 a α)
        ( tree-𝕎 b β)
        {!!} ,
        {!!})

  is-proof-irrelevant-fib-enriched-directed-tree-element-𝕎 :
    (w : 𝕎 A B) →
    is-contr
      ( Σ ( 𝕎 A B)
          ( λ v →
            equiv-Enriched-Directed-Tree A B
              ( enriched-directed-tree-element-𝕎 v)
              ( enriched-directed-tree-element-𝕎 w)))
  is-proof-irrelevant-fib-enriched-directed-tree-element-𝕎 w = {!!}
```
