# The underlying trees of elements of coalgebras of polynomial endofunctors

```agda
module trees.underlying-trees-elements-coalgebras-polynomial-endofunctors where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.isolated-elements
open import foundation.negated-equality
open import foundation.propositions
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-empty-type
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.morphisms-directed-graphs
open import graph-theory.walks-directed-graphs

open import trees.coalgebras-polynomial-endofunctors
open import trees.combinator-directed-trees
open import trees.combinator-enriched-directed-trees
open import trees.directed-trees
open import trees.elementhood-relation-coalgebras-polynomial-endofunctors
open import trees.enriched-directed-trees
open import trees.equivalences-directed-trees
open import trees.equivalences-enriched-directed-trees
open import trees.polynomial-endofunctors
```

</details>

## Idea

For every element `x` of a
[coalgebra](trees.coalgebras-polynomial-endofunctors.md) of a
[polynomial endofunctor](trees.polynomial-endofunctors.md) we can inductively
define an [enriched directed tree](trees.enriched-directed-trees.md). This tree
is called the
{{#concept "underlying enriched directed tree" Disambiguation="of an element of a coalgebra of a polynomial endofunctor" Agda=enriched-directed-tree-element-coalgebra}}
of `x`.

## Definition

### The underlying graph of an element of a coalgebra of a polynomial endofunctor

```agda
module _
  {l1 l2 l3 : Level}
  {P : polynomial-endofunctor l1 l2}
  (X : coalgebra-polynomial-endofunctor l3 P)
  where

  data
    node-element-coalgebra :
      type-coalgebra-polynomial-endofunctor X → UU (l2 ⊔ l3)
    where
    root-coalgebra :
      (w : type-coalgebra-polynomial-endofunctor X) →
      node-element-coalgebra w
    node-inclusion-element-coalgebra :
      {u v : type-coalgebra-polynomial-endofunctor X} →
      (u ∈ v in-coalgebra X) →
      node-element-coalgebra u →
      node-element-coalgebra v

  data
    edge-element-coalgebra :
      (w : type-coalgebra-polynomial-endofunctor X)
      (x y : node-element-coalgebra w) → UU (l2 ⊔ l3)
    where
    edge-to-root-element-coalgebra :
      {u v : type-coalgebra-polynomial-endofunctor X}
      (H : u ∈ v in-coalgebra X) →
      edge-element-coalgebra v
        ( node-inclusion-element-coalgebra H
          ( root-coalgebra u))
        ( root-coalgebra v)
    edge-inclusion-element-coalgebra :
      {u v : type-coalgebra-polynomial-endofunctor X}
      (H : u ∈ v in-coalgebra X) →
      {x y : node-element-coalgebra u}
      (e : edge-element-coalgebra u x y) →
      edge-element-coalgebra v
        ( node-inclusion-element-coalgebra H x)
        ( node-inclusion-element-coalgebra H y)

  graph-element-coalgebra :
    type-coalgebra-polynomial-endofunctor X →
    Directed-Graph (l2 ⊔ l3) (l2 ⊔ l3)
  pr1 (graph-element-coalgebra w) =
    node-element-coalgebra w
  pr2 (graph-element-coalgebra w) =
    edge-element-coalgebra w

  walk-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X)
    (x y : node-element-coalgebra w) → UU (l2 ⊔ l3)
  walk-element-coalgebra w =
    walk-Directed-Graph (graph-element-coalgebra w)
```

### The external graph of an element of a W-type

```agda
  node-external-graph-element-coalgebra :
    type-coalgebra-polynomial-endofunctor X → UU (l2 ⊔ l3)
  node-external-graph-element-coalgebra w =
    Σ ( type-coalgebra-polynomial-endofunctor X)
      ( λ u → walk-coalgebra-polynomial-endofunctor X u w)

  edge-external-graph-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X)
    (x y : node-external-graph-element-coalgebra w) →
    UU (l2 ⊔ l3)
  edge-external-graph-element-coalgebra
    w (x , H) (y , K) =
    Σ ( x ∈ y in-coalgebra X) (λ e → cons-walk-Directed-Graph e K ＝ H)

  external-graph-element-coalgebra :
    type-coalgebra-polynomial-endofunctor X → Directed-Graph (l2 ⊔ l3) (l2 ⊔ l3)
  pr1 (external-graph-element-coalgebra w) =
    node-external-graph-element-coalgebra w
  pr2 (external-graph-element-coalgebra w) =
    edge-external-graph-element-coalgebra w
```

## Properties

### To be a root is decidable

```agda
module _
  {l1 l2 l3 : Level} {P : polynomial-endofunctor l1 l2}
  (X : coalgebra-polynomial-endofunctor l3 P)
  where

  is-root-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X) →
    node-element-coalgebra X w → UU (l2 ⊔ l3)
  is-root-element-coalgebra w x =
    root-coalgebra w ＝ x

  is-isolated-root-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X) →
    is-isolated (root-coalgebra {X = X} w)
  is-isolated-root-element-coalgebra w
    ( root-coalgebra w) =
    inl refl
  is-isolated-root-element-coalgebra w
    ( node-inclusion-element-coalgebra H y) =
    inr (λ ())

  is-contr-loop-space-root-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X) →
    is-contr
      ( root-coalgebra w ＝
        root-coalgebra w)
  is-contr-loop-space-root-element-coalgebra w =
    is-contr-loop-space-isolated-element
      ( root-coalgebra w)
      ( is-isolated-root-element-coalgebra w)
```

### Characterization of equality of the type of nodes of the underlying graph of an element of `coalgebra A B`

```agda
module _
  {l1 l2 l3 : Level} {P : polynomial-endofunctor l1 l2}
  (X : coalgebra-polynomial-endofunctor l3 P)
  where

  data
    Eq-node-element-coalgebra
      ( w : type-coalgebra-polynomial-endofunctor X) :
      ( x y : node-element-coalgebra X w) → UU (l2 ⊔ l3)
    where
    root-refl-Eq-node-element-coalgebra :
      Eq-node-element-coalgebra w
        ( root-coalgebra w)
        ( root-coalgebra w)
    node-inclusion-Eq-node-element-coalgebra :
      {u : type-coalgebra-polynomial-endofunctor X}
      (H : u ∈ w in-coalgebra X)
      {x y : node-element-coalgebra X u} →
      Eq-node-element-coalgebra u x y →
      Eq-node-element-coalgebra w
        ( node-inclusion-element-coalgebra H x)
        ( node-inclusion-element-coalgebra H y)

  refl-Eq-node-element-coalgebra :
    {w : type-coalgebra-polynomial-endofunctor X}
    (x : node-element-coalgebra X w) →
    Eq-node-element-coalgebra w x x
  refl-Eq-node-element-coalgebra
    ( root-coalgebra w) =
    root-refl-Eq-node-element-coalgebra
  refl-Eq-node-element-coalgebra
    ( node-inclusion-element-coalgebra {u} H x) =
    node-inclusion-Eq-node-element-coalgebra H
      ( refl-Eq-node-element-coalgebra x)

  center-total-Eq-node-element-coalgebra :
    {w : type-coalgebra-polynomial-endofunctor X}
    (x : node-element-coalgebra X w) →
    Σ ( node-element-coalgebra X w)
      ( Eq-node-element-coalgebra w x)
  pr1 (center-total-Eq-node-element-coalgebra x) = x
  pr2 (center-total-Eq-node-element-coalgebra x) =
    refl-Eq-node-element-coalgebra x

  contraction-total-Eq-node-element-coalgebra :
    {w : type-coalgebra-polynomial-endofunctor X}
    (x : node-element-coalgebra X w) →
    (u :
      Σ ( node-element-coalgebra X w)
        ( Eq-node-element-coalgebra w x)) →
    center-total-Eq-node-element-coalgebra x ＝ u
  contraction-total-Eq-node-element-coalgebra ._
    (._ , root-refl-Eq-node-element-coalgebra) =
    refl
  contraction-total-Eq-node-element-coalgebra ._
    ( .(node-inclusion-element-coalgebra H _) ,
      node-inclusion-Eq-node-element-coalgebra H e) =
    ap
      ( map-Σ
        ( λ z → Eq-node-element-coalgebra _ _ z)
        ( node-inclusion-element-coalgebra H)
        ( λ y →
          node-inclusion-Eq-node-element-coalgebra H))
      ( contraction-total-Eq-node-element-coalgebra _
        ( _ , e))

  is-torsorial-Eq-node-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X)
    (x : node-element-coalgebra X w) →
    is-torsorial (Eq-node-element-coalgebra w x)
  pr1 (is-torsorial-Eq-node-element-coalgebra w x) =
    center-total-Eq-node-element-coalgebra x
  pr2 (is-torsorial-Eq-node-element-coalgebra w x) =
    contraction-total-Eq-node-element-coalgebra x

  Eq-eq-node-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X)
    {x y : node-element-coalgebra X w} →
    x ＝ y → Eq-node-element-coalgebra w x y
  Eq-eq-node-element-coalgebra w refl =
    refl-Eq-node-element-coalgebra _

  is-equiv-Eq-eq-node-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X)
    (x y : node-element-coalgebra X w) →
    is-equiv (Eq-eq-node-element-coalgebra w {x} {y})
  is-equiv-Eq-eq-node-element-coalgebra w x =
    fundamental-theorem-id
      ( is-torsorial-Eq-node-element-coalgebra w x)
      ( λ y → Eq-eq-node-element-coalgebra w {x} {y})

  extensionality-node-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X)
    (x y : node-element-coalgebra X w) →
    (x ＝ y) ≃ Eq-node-element-coalgebra w x y
  pr1 (extensionality-node-element-coalgebra w x y) =
    Eq-eq-node-element-coalgebra w {x} {y}
  pr2 (extensionality-node-element-coalgebra w x y) =
    is-equiv-Eq-eq-node-element-coalgebra w x y

  eq-Eq-node-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X)
    (x y : node-element-coalgebra X w) →
    Eq-node-element-coalgebra w x y → x ＝ y
  eq-Eq-node-element-coalgebra w x y =
    map-inv-equiv
      ( extensionality-node-element-coalgebra w x y)
```

Note that we don't expect that `node-inclusion-element-coalgebra'` is an
embedding. The total space `Σ (y : B x), node-element-coalgebra' (α y)` embeds
into `node-element-coalgebra' (tree-coalgebra x α)`, and this implies that the
node inclusion has the same truncation level as the fiber inclusions

```text
  node-element-coalgebra' (α b) → Σ (y : B x), node-element-coalgebra' (α y)
```

In other words, the fiber is `Ω (B , b)`.

### For any `u ∈-coalgebra v` in `coalgebra A B` we have a graph inclusion from the underlying graph of `u` to the underlying graph of `v`

```agda
module _
  {l1 l2 l3 : Level} {P : polynomial-endofunctor l1 l2}
  (X : coalgebra-polynomial-endofunctor l3 P)
  where

  inclusion-element-coalgebra :
    {u v : type-coalgebra-polynomial-endofunctor X} →
    u ∈ v in-coalgebra X →
    hom-Directed-Graph
      ( graph-element-coalgebra X u)
      ( graph-element-coalgebra X v)
  pr1 (inclusion-element-coalgebra {u} {v} H) =
    node-inclusion-element-coalgebra H
  pr2
    ( inclusion-element-coalgebra {u} {v} H)
    x y e =
    edge-inclusion-element-coalgebra H e

  walk-inclusion-element-coalgebra :
    {u v : type-coalgebra-polynomial-endofunctor X} →
    (H : u ∈ v in-coalgebra X) →
    {x y : node-element-coalgebra X u} →
    walk-element-coalgebra X u x y →
    walk-element-coalgebra X v
      ( node-inclusion-element-coalgebra H x)
      ( node-inclusion-element-coalgebra H y)
  walk-inclusion-element-coalgebra {u} {v} H =
    walk-hom-Directed-Graph
      ( graph-element-coalgebra X u)
      ( graph-element-coalgebra X v)
      ( inclusion-element-coalgebra H)
```

### The type of edges from the root of `u ∈-coalgebra v` to the root of `v` is contractible

```agda
module _
  {l1 l2 l3 : Level} {P : polynomial-endofunctor l1 l2}
  (X : coalgebra-polynomial-endofunctor l3 P)
  where

  is-contr-edge-to-root-element-coalgebra :
    {u v : type-coalgebra-polynomial-endofunctor X}
    (H : u ∈ v in-coalgebra X) →
    is-contr
      ( edge-element-coalgebra X v
        ( node-inclusion-element-coalgebra H
          ( root-coalgebra u))
        ( root-coalgebra v))
  pr1 (is-contr-edge-to-root-element-coalgebra H) =
    edge-to-root-element-coalgebra H
  pr2
    ( is-contr-edge-to-root-element-coalgebra H)
    ( edge-to-root-element-coalgebra .H) =
    refl
```

### The type of edges from any node to the root is a proposition

```agda
module _
  {l1 l2 l3 : Level} {P : polynomial-endofunctor l1 l2}
  (X : coalgebra-polynomial-endofunctor l3 P)
  where

  is-proof-irrelevant-edge-to-root-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X)
    (x : node-element-coalgebra X w) →
    is-proof-irrelevant
      ( edge-element-coalgebra X w x
        ( root-coalgebra w))
  is-proof-irrelevant-edge-to-root-element-coalgebra w ._
    ( edge-to-root-element-coalgebra H) =
    is-contr-edge-to-root-element-coalgebra X H

  is-prop-edge-to-root-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X)
    (x : node-element-coalgebra X w) →
    is-prop
      ( edge-element-coalgebra X w x
        ( root-coalgebra w))
  is-prop-edge-to-root-element-coalgebra w x =
    is-prop-is-proof-irrelevant
      ( is-proof-irrelevant-edge-to-root-element-coalgebra
        w x)
```

### The underlying graph of any element of a W-type is a directed tree

```agda
module _
  {l1 l2 l3 : Level} {P : polynomial-endofunctor l1 l2}
  (X : coalgebra-polynomial-endofunctor l3 P)
  where

  no-edge-from-root-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X) →
    is-empty
      ( Σ ( node-element-coalgebra X w)
          ( edge-element-coalgebra X w
            ( root-coalgebra w)))
  no-edge-from-root-element-coalgebra w (x , ())

  is-empty-eq-root-node-inclusion-element-coalgebra :
    {v w : type-coalgebra-polynomial-endofunctor X}
    (H : v ∈ w in-coalgebra X)
    (x : node-element-coalgebra X v) →
    root-coalgebra w ≠ node-inclusion-element-coalgebra H x
  is-empty-eq-root-node-inclusion-element-coalgebra
    H x ()

  has-unique-predecessor-node-inclusion-element-coalgebra :
    {v w : type-coalgebra-polynomial-endofunctor X}
    (H : v ∈ w in-coalgebra X)
    (x : node-element-coalgebra X v) →
    is-contr
      ( Σ ( node-element-coalgebra X w)
          ( edge-element-coalgebra X w
            ( node-inclusion-element-coalgebra H x)))
  pr1
    ( pr1
      ( has-unique-predecessor-node-inclusion-element-coalgebra H
        ( root-coalgebra w))) =
    root-coalgebra _
  pr2
    ( pr1
      ( has-unique-predecessor-node-inclusion-element-coalgebra H
        ( root-coalgebra w))) =
    edge-to-root-element-coalgebra H
  pr2
    ( has-unique-predecessor-node-inclusion-element-coalgebra H
      ( root-coalgebra w))
    ( ._ , edge-to-root-element-coalgebra .H) =
    refl
  pr1
    ( has-unique-predecessor-node-inclusion-element-coalgebra H
      ( node-inclusion-element-coalgebra K x)) =
    map-Σ
      ( λ y →
        edge-element-coalgebra X _
          ( node-inclusion-element-coalgebra H
            ( node-inclusion-element-coalgebra K x))
          ( y))
      ( node-inclusion-element-coalgebra H)
      ( λ y → edge-inclusion-element-coalgebra H)
      ( center
        ( has-unique-predecessor-node-inclusion-element-coalgebra K x))
  pr2
    ( has-unique-predecessor-node-inclusion-element-coalgebra H
      ( node-inclusion-element-coalgebra K x))
    ( .(node-inclusion-element-coalgebra H _) ,
      edge-inclusion-element-coalgebra .H f) =
    ap
      ( map-Σ _
        ( node-inclusion-element-coalgebra H)
        ( λ y → edge-inclusion-element-coalgebra H))
      ( eq-is-contr
        ( has-unique-predecessor-node-inclusion-element-coalgebra K x))

  has-unique-predecessor-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X)
    (x : node-element-coalgebra X w) →
    is-contr
      ( ( root-coalgebra w ＝ x) +
        ( Σ ( node-element-coalgebra X w)
            ( edge-element-coalgebra X w x)))
  has-unique-predecessor-element-coalgebra w
    ( root-coalgebra w) =
    is-contr-equiv
      ( root-coalgebra w ＝
        root-coalgebra w)
      ( right-unit-law-coproduct-is-empty
        ( root-coalgebra w ＝
          root-coalgebra w)
        ( Σ ( node-element-coalgebra X w)
            ( edge-element-coalgebra X w
              ( root-coalgebra w)))
        ( no-edge-from-root-element-coalgebra w))
      ( is-contr-loop-space-root-element-coalgebra
        ( X)
        ( w))
  has-unique-predecessor-element-coalgebra w
    ( node-inclusion-element-coalgebra H x) =
    is-contr-equiv
      ( Σ ( node-element-coalgebra X w)
          ( edge-element-coalgebra X w
            ( node-inclusion-element-coalgebra H x)))
      ( left-unit-law-coproduct-is-empty
        ( root-coalgebra w ＝
          node-inclusion-element-coalgebra H x)
        ( Σ ( node-element-coalgebra X w)
            ( edge-element-coalgebra X w
              ( node-inclusion-element-coalgebra H x)))
        ( is-empty-eq-root-node-inclusion-element-coalgebra H x))
      ( has-unique-predecessor-node-inclusion-element-coalgebra H x)

  walk-to-root-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X)
    (x : node-element-coalgebra X w) →
    walk-element-coalgebra X w x (root-coalgebra w)
  walk-to-root-element-coalgebra w
    ( root-coalgebra w) =
    refl-walk-Directed-Graph
  walk-to-root-element-coalgebra w
    ( node-inclusion-element-coalgebra {v} H x) =
    snoc-walk-Directed-Graph
      ( graph-element-coalgebra X w)
      ( walk-hom-Directed-Graph
        ( graph-element-coalgebra X v)
        ( graph-element-coalgebra X w)
        ( inclusion-element-coalgebra X H)
        ( walk-to-root-element-coalgebra v x))
      ( edge-to-root-element-coalgebra H)

  unique-walk-to-root-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X) →
    is-tree-Directed-Graph'
      ( graph-element-coalgebra X w)
      ( root-coalgebra w)
  unique-walk-to-root-element-coalgebra w =
    is-tree-unique-direct-successor-Directed-Graph'
      ( graph-element-coalgebra X w)
      ( root-coalgebra w)
      ( has-unique-predecessor-element-coalgebra w)
      ( walk-to-root-element-coalgebra w)

  directed-tree-element-coalgebra :
    type-coalgebra-polynomial-endofunctor X → Directed-Tree (l2 ⊔ l3) (l2 ⊔ l3)
  pr1 (directed-tree-element-coalgebra w) =
    graph-element-coalgebra X w
  pr1 (pr2 (directed-tree-element-coalgebra w)) =
    root-coalgebra w
  pr2 (pr2 (directed-tree-element-coalgebra w)) =
    unique-walk-to-root-element-coalgebra w
```

### The underlying graph of an element of a W-type can be given the structure of an enriched directed tree

```agda
module _
  {l1 l2 l3 : Level} {P : polynomial-endofunctor l1 l2}
  (X : coalgebra-polynomial-endofunctor l3 P)
  where

  shape-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X) →
    node-element-coalgebra X w → shape-polynomial-endofunctor P
  shape-element-coalgebra w
    ( root-coalgebra w) =
    shape-coalgebra-polynomial-endofunctor X w
  shape-element-coalgebra w
    ( node-inclusion-element-coalgebra {u} H y) =
    shape-element-coalgebra u y

  map-enrichment-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X)
    (x : node-element-coalgebra X w) →
    position-polynomial-endofunctor P (shape-element-coalgebra w x) →
    Σ ( node-element-coalgebra X w)
      ( λ y → edge-element-coalgebra X w y x)
  pr1
    ( map-enrichment-element-coalgebra w
      ( root-coalgebra w) b) =
    node-inclusion-element-coalgebra
      ( b , refl)
      ( root-coalgebra (pr2 (pr2 X w) b))
  pr2
    ( map-enrichment-element-coalgebra w
      ( root-coalgebra w)
      ( b)) =
    edge-to-root-element-coalgebra (b , refl)
  map-enrichment-element-coalgebra w
    ( node-inclusion-element-coalgebra {u} H y) b =
    map-Σ
      ( λ z →
        edge-element-coalgebra X w z
          ( node-inclusion-element-coalgebra H y))
      ( node-inclusion-element-coalgebra H)
      ( λ z → edge-inclusion-element-coalgebra H)
      ( map-enrichment-element-coalgebra
        ( u)
        ( y)
        ( b))

  map-inv-enrichment-directed-tree-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X)
    (x : node-element-coalgebra X w) →
    Σ ( node-element-coalgebra X w)
      ( λ y → edge-element-coalgebra X w y x) →
    position-polynomial-endofunctor P (shape-element-coalgebra w x)
  map-inv-enrichment-directed-tree-element-coalgebra w ._
    ( ._ , edge-to-root-element-coalgebra H) =
    pr1 H
  map-inv-enrichment-directed-tree-element-coalgebra w ._
    ( ._ ,
      edge-inclusion-element-coalgebra {u} H {x} {y} e) =
    map-inv-enrichment-directed-tree-element-coalgebra
      ( u)
      ( y)
      ( x , e)

  is-section-map-inv-enrichment-directed-tree-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X)
    (x : node-element-coalgebra X w) →
    ( ( map-enrichment-element-coalgebra
        w x) ∘
      ( map-inv-enrichment-directed-tree-element-coalgebra
      w x)) ~ id
  is-section-map-inv-enrichment-directed-tree-element-coalgebra w ._
    ( ._ , edge-to-root-element-coalgebra (b , refl)) =
    refl
  is-section-map-inv-enrichment-directed-tree-element-coalgebra w ._
    ( ._ ,
      edge-inclusion-element-coalgebra {u} H {x} {y} e) =
    ap
      ( map-Σ
        ( λ z →
          edge-element-coalgebra X w z
            ( node-inclusion-element-coalgebra H y))
        ( node-inclusion-element-coalgebra H)
        ( λ z → edge-inclusion-element-coalgebra H))
      ( is-section-map-inv-enrichment-directed-tree-element-coalgebra u y
        ( x , e))

  is-retraction-map-inv-enrichment-directed-tree-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X)
    (x : node-element-coalgebra X w) →
    ( map-inv-enrichment-directed-tree-element-coalgebra w x ∘
      map-enrichment-element-coalgebra w x) ~ id
  is-retraction-map-inv-enrichment-directed-tree-element-coalgebra w
    ( root-coalgebra w) b =
    refl
  is-retraction-map-inv-enrichment-directed-tree-element-coalgebra w
    ( node-inclusion-element-coalgebra {u} H y) b =
    is-retraction-map-inv-enrichment-directed-tree-element-coalgebra u y b

  is-equiv-map-enrichment-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X)
    (x : node-element-coalgebra X w) →
    is-equiv (map-enrichment-element-coalgebra w x)
  is-equiv-map-enrichment-element-coalgebra w x =
    is-equiv-is-invertible
      ( map-inv-enrichment-directed-tree-element-coalgebra w x)
      ( is-section-map-inv-enrichment-directed-tree-element-coalgebra w x)
      ( is-retraction-map-inv-enrichment-directed-tree-element-coalgebra w x)

  enrichment-directed-tree-element-coalgebra :
    (w : type-coalgebra-polynomial-endofunctor X)
    (x : node-element-coalgebra X w) →
    position-polynomial-endofunctor P (shape-element-coalgebra w x) ≃
    Σ ( node-element-coalgebra X w)
      ( λ y → edge-element-coalgebra X w y x)
  pr1 (enrichment-directed-tree-element-coalgebra w x) =
    map-enrichment-element-coalgebra w x
  pr2 (enrichment-directed-tree-element-coalgebra w x) =
    is-equiv-map-enrichment-element-coalgebra w x

  enriched-directed-tree-element-coalgebra :
    type-coalgebra-polynomial-endofunctor X →
    Enriched-Directed-Tree (l2 ⊔ l3) (l2 ⊔ l3)
      ( shape-polynomial-endofunctor P)
      ( position-polynomial-endofunctor P)
  pr1 (enriched-directed-tree-element-coalgebra w) =
    directed-tree-element-coalgebra X w
  pr1
    ( pr2 (enriched-directed-tree-element-coalgebra w)) =
    shape-element-coalgebra w
  pr2
    ( pr2 (enriched-directed-tree-element-coalgebra w)) =
    enrichment-directed-tree-element-coalgebra w
```

### The underlying tree of `w` is the combinator tree of the underlying trees of `component X w b` indexed by `b : B (shape w)`

```agda
module _
  {l1 l2 l3 : Level} {P : polynomial-endofunctor l1 l2}
  (X : coalgebra-polynomial-endofunctor l3 P)
  (w : type-coalgebra-polynomial-endofunctor X)
  where

  node-compute-directed-tree-element-coalgebra :
    node-element-coalgebra X w →
    node-combinator-Directed-Tree
      ( λ b → directed-tree-element-coalgebra X
        ( component-coalgebra-polynomial-endofunctor X w b))
  node-compute-directed-tree-element-coalgebra
    ( root-coalgebra w) =
    root-combinator-Directed-Tree
  node-compute-directed-tree-element-coalgebra
    ( node-inclusion-element-coalgebra (b , refl) x) =
    node-inclusion-combinator-Directed-Tree b x

  map-inv-node-compute-directed-tree-element-coalgebra :
    node-combinator-Directed-Tree
      ( λ b →
        directed-tree-element-coalgebra X
          ( component-coalgebra-polynomial-endofunctor X w b)) →
    node-element-coalgebra X w
  map-inv-node-compute-directed-tree-element-coalgebra
    root-combinator-Directed-Tree =
    root-coalgebra _
  map-inv-node-compute-directed-tree-element-coalgebra
    ( node-inclusion-combinator-Directed-Tree b x) =
    node-inclusion-element-coalgebra (b , refl) x

  is-section-map-inv-node-compute-directed-tree-element-coalgebra :
    ( node-compute-directed-tree-element-coalgebra ∘
      map-inv-node-compute-directed-tree-element-coalgebra) ~ id
  is-section-map-inv-node-compute-directed-tree-element-coalgebra
    root-combinator-Directed-Tree =
    refl
  is-section-map-inv-node-compute-directed-tree-element-coalgebra
    ( node-inclusion-combinator-Directed-Tree i x) =
    refl

  is-retraction-map-inv-node-compute-directed-tree-element-coalgebra :
    ( map-inv-node-compute-directed-tree-element-coalgebra ∘
      node-compute-directed-tree-element-coalgebra) ~ id
  is-retraction-map-inv-node-compute-directed-tree-element-coalgebra
    ( root-coalgebra w) =
    refl
  is-retraction-map-inv-node-compute-directed-tree-element-coalgebra
    ( node-inclusion-element-coalgebra (b , refl) x) =
    refl

  is-node-equiv-compute-directed-tree-element-coalgebra :
    is-equiv node-compute-directed-tree-element-coalgebra
  is-node-equiv-compute-directed-tree-element-coalgebra =
    is-equiv-is-invertible
      map-inv-node-compute-directed-tree-element-coalgebra
      is-section-map-inv-node-compute-directed-tree-element-coalgebra
      is-retraction-map-inv-node-compute-directed-tree-element-coalgebra

  node-equiv-compute-directed-tree-element-coalgebra :
    node-element-coalgebra X w ≃
    node-combinator-Directed-Tree
      ( λ b →
        directed-tree-element-coalgebra X
          ( component-coalgebra-polynomial-endofunctor X w b))
  pr1 node-equiv-compute-directed-tree-element-coalgebra =
    node-compute-directed-tree-element-coalgebra
  pr2 node-equiv-compute-directed-tree-element-coalgebra =
    is-node-equiv-compute-directed-tree-element-coalgebra

  edge-compute-directed-tree-element-coalgebra :
    (x y : node-element-coalgebra X w) →
    edge-element-coalgebra X w x y →
    edge-combinator-Directed-Tree
      ( λ b →
        directed-tree-element-coalgebra X
          ( component-coalgebra-polynomial-endofunctor X w b))
      ( node-compute-directed-tree-element-coalgebra x)
      ( node-compute-directed-tree-element-coalgebra y)
  edge-compute-directed-tree-element-coalgebra ._ ._
    ( edge-to-root-element-coalgebra (b , refl)) =
    edge-to-root-combinator-Directed-Tree b
  edge-compute-directed-tree-element-coalgebra ._ ._
    ( edge-inclusion-element-coalgebra (b , refl) e) =
    edge-inclusion-combinator-Directed-Tree b _ _ e

  map-inv-edge-compute-directed-tree-element-coalgebra' :
    ( x y :
      node-combinator-Directed-Tree
        ( directed-tree-element-coalgebra X ∘
          component-coalgebra-polynomial-endofunctor X w)) →
    edge-combinator-Directed-Tree
      ( λ b →
        directed-tree-element-coalgebra X
          ( component-coalgebra-polynomial-endofunctor X w b))
      ( x)
      ( y) →
    edge-element-coalgebra X w
      ( map-inv-node-compute-directed-tree-element-coalgebra x)
      ( map-inv-node-compute-directed-tree-element-coalgebra y)
  map-inv-edge-compute-directed-tree-element-coalgebra' ._ ._
    ( edge-to-root-combinator-Directed-Tree b) =
    edge-to-root-element-coalgebra (b , refl)
  map-inv-edge-compute-directed-tree-element-coalgebra' ._ ._
    ( edge-inclusion-combinator-Directed-Tree b x y e) =
    edge-inclusion-element-coalgebra (b , refl) e

  map-inv-edge-compute-directed-tree-element-coalgebra :
    ( x y : node-element-coalgebra X w) →
    edge-combinator-Directed-Tree
      ( λ b →
        directed-tree-element-coalgebra X
          ( component-coalgebra-polynomial-endofunctor X w b))
      ( node-compute-directed-tree-element-coalgebra x)
      ( node-compute-directed-tree-element-coalgebra y) →
    edge-element-coalgebra X w x y
  map-inv-edge-compute-directed-tree-element-coalgebra x y =
    ( binary-tr
      ( edge-element-coalgebra X w)
      ( is-retraction-map-inv-node-compute-directed-tree-element-coalgebra x)
      ( is-retraction-map-inv-node-compute-directed-tree-element-coalgebra y)) ∘
    ( map-inv-edge-compute-directed-tree-element-coalgebra'
      ( node-compute-directed-tree-element-coalgebra x)
      ( node-compute-directed-tree-element-coalgebra y))

  is-section-map-inv-edge-compute-directed-tree-element-coalgebra' :
    ( x y :
      node-combinator-Directed-Tree
        ( directed-tree-element-coalgebra X ∘
          component-coalgebra-polynomial-endofunctor X w)) →
    ( e :
      edge-combinator-Directed-Tree
        ( λ b →
          directed-tree-element-coalgebra X
            ( component-coalgebra-polynomial-endofunctor X w b))
        ( x)
        ( y)) →
    binary-tr
      ( edge-combinator-Directed-Tree
        ( λ b →
          directed-tree-element-coalgebra X
            ( component-coalgebra-polynomial-endofunctor X w b)))
      ( is-section-map-inv-node-compute-directed-tree-element-coalgebra x)
      ( is-section-map-inv-node-compute-directed-tree-element-coalgebra y)
      ( edge-compute-directed-tree-element-coalgebra
        ( map-inv-node-compute-directed-tree-element-coalgebra x)
        ( map-inv-node-compute-directed-tree-element-coalgebra y)
        ( map-inv-edge-compute-directed-tree-element-coalgebra' x y e)) ＝ e
  is-section-map-inv-edge-compute-directed-tree-element-coalgebra' ._ ._
    ( edge-to-root-combinator-Directed-Tree i) =
    refl
  is-section-map-inv-edge-compute-directed-tree-element-coalgebra' ._ ._
    ( edge-inclusion-combinator-Directed-Tree i x y e) =
    refl

  is-section-map-inv-edge-compute-directed-tree-element-coalgebra :
    (x y : node-element-coalgebra X w) →
    ( e :
      edge-combinator-Directed-Tree
        ( λ b →
          directed-tree-element-coalgebra X
            ( component-coalgebra-polynomial-endofunctor X w b))
        ( node-compute-directed-tree-element-coalgebra x)
        ( node-compute-directed-tree-element-coalgebra y)) →
    edge-compute-directed-tree-element-coalgebra x y
      ( map-inv-edge-compute-directed-tree-element-coalgebra x y e) ＝ e
  is-section-map-inv-edge-compute-directed-tree-element-coalgebra
    ( node-inclusion-element-coalgebra (b , refl) x)
    ( root-coalgebra _)
    ( e) =
    is-section-map-inv-edge-compute-directed-tree-element-coalgebra'
      ( node-compute-directed-tree-element-coalgebra _)
      ( node-compute-directed-tree-element-coalgebra _)
      ( e)
  is-section-map-inv-edge-compute-directed-tree-element-coalgebra
    ( node-inclusion-element-coalgebra (b , refl) x)
    ( node-inclusion-element-coalgebra (c , refl) y)
    ( e) =
    is-section-map-inv-edge-compute-directed-tree-element-coalgebra'
      ( node-compute-directed-tree-element-coalgebra _)
      ( node-compute-directed-tree-element-coalgebra _)
      ( e)

  is-retraction-map-inv-edge-compute-directed-tree-element-coalgebra :
    (x y : node-element-coalgebra X w) (e : edge-element-coalgebra X w x y) →
    map-inv-edge-compute-directed-tree-element-coalgebra x y
      ( edge-compute-directed-tree-element-coalgebra x y e) ＝ e
  is-retraction-map-inv-edge-compute-directed-tree-element-coalgebra ._ ._
    ( edge-to-root-element-coalgebra (b , refl)) = refl
  is-retraction-map-inv-edge-compute-directed-tree-element-coalgebra ._ ._
    ( edge-inclusion-element-coalgebra (b , refl) e) = refl

  is-edge-equiv-compute-directed-tree-element-coalgebra :
    (x y : node-element-coalgebra X w) →
    is-equiv (edge-compute-directed-tree-element-coalgebra x y)
  is-edge-equiv-compute-directed-tree-element-coalgebra x y =
    is-equiv-is-invertible
      ( map-inv-edge-compute-directed-tree-element-coalgebra x y)
      ( is-section-map-inv-edge-compute-directed-tree-element-coalgebra x y)
      ( is-retraction-map-inv-edge-compute-directed-tree-element-coalgebra x y)

  edge-equiv-compute-directed-tree-element-coalgebra :
    (x y : node-element-coalgebra X w) →
    edge-element-coalgebra X w x y ≃
    edge-combinator-Directed-Tree
      ( λ b →
        directed-tree-element-coalgebra X
          ( component-coalgebra-polynomial-endofunctor X w b))
      ( node-compute-directed-tree-element-coalgebra x)
      ( node-compute-directed-tree-element-coalgebra y)
  pr1 (edge-equiv-compute-directed-tree-element-coalgebra x y) =
    edge-compute-directed-tree-element-coalgebra x y
  pr2 (edge-equiv-compute-directed-tree-element-coalgebra x y) =
    is-edge-equiv-compute-directed-tree-element-coalgebra x y

  compute-directed-tree-element-coalgebra :
    equiv-Directed-Tree
      ( directed-tree-element-coalgebra X w)
      ( combinator-Directed-Tree
        ( λ b →
          directed-tree-element-coalgebra X
            ( component-coalgebra-polynomial-endofunctor X w b)))
  pr1 compute-directed-tree-element-coalgebra =
    node-equiv-compute-directed-tree-element-coalgebra
  pr2 compute-directed-tree-element-coalgebra =
    edge-equiv-compute-directed-tree-element-coalgebra

  shape-compute-enriched-directed-tree-element-coalgebra :
    shape-element-coalgebra X w ~
    ( ( shape-combinator-Enriched-Directed-Tree
        ( shape-polynomial-endofunctor P)
        ( position-polynomial-endofunctor P)
        ( λ b →
          enriched-directed-tree-element-coalgebra X
            ( component-coalgebra-polynomial-endofunctor X w b))) ∘
      ( node-compute-directed-tree-element-coalgebra))
  shape-compute-enriched-directed-tree-element-coalgebra (root-coalgebra _) =
    refl
  shape-compute-enriched-directed-tree-element-coalgebra
    ( node-inclusion-element-coalgebra (b , refl) x) =
    refl

  enrichment-compute-enriched-directed-tree-element-coalgebra :
    (x : node-element-coalgebra X w) →
    htpy-equiv
      ( ( equiv-direct-predecessor-equiv-Directed-Tree
          ( directed-tree-element-coalgebra X w)
          ( combinator-Directed-Tree
            ( λ b →
              directed-tree-element-coalgebra X
                ( component-coalgebra-polynomial-endofunctor X w b)))
          ( compute-directed-tree-element-coalgebra)
          ( x)) ∘e
        ( enrichment-directed-tree-element-coalgebra X w x))
      ( ( enrichment-combinator-Enriched-Directed-Tree
          ( shape-polynomial-endofunctor P)
          ( position-polynomial-endofunctor P)
          ( λ b →
            enriched-directed-tree-element-coalgebra X
              ( component-coalgebra-polynomial-endofunctor X w b))
          ( node-compute-directed-tree-element-coalgebra x)) ∘e
        ( equiv-tr
          ( position-polynomial-endofunctor P)
          ( shape-compute-enriched-directed-tree-element-coalgebra x)))
  enrichment-compute-enriched-directed-tree-element-coalgebra
    ( root-coalgebra _)
    ( b) = refl
  enrichment-compute-enriched-directed-tree-element-coalgebra
    ( node-inclusion-element-coalgebra (c , refl) x) b =
    refl

  compute-enriched-directed-tree-element-coalgebra :
    equiv-Enriched-Directed-Tree
      ( shape-polynomial-endofunctor P)
      ( position-polynomial-endofunctor P)
      ( enriched-directed-tree-element-coalgebra X w)
      ( combinator-Enriched-Directed-Tree
        ( shape-polynomial-endofunctor P)
        ( position-polynomial-endofunctor P)
        ( λ b →
          enriched-directed-tree-element-coalgebra X
            ( component-coalgebra-polynomial-endofunctor X w b)))
  pr1 compute-enriched-directed-tree-element-coalgebra =
    compute-directed-tree-element-coalgebra
  pr1 (pr2 compute-enriched-directed-tree-element-coalgebra) =
    shape-compute-enriched-directed-tree-element-coalgebra
  pr2 (pr2 compute-enriched-directed-tree-element-coalgebra) =
    enrichment-compute-enriched-directed-tree-element-coalgebra
```
