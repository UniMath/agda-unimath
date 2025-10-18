# Directed trees

```agda
module trees.directed-trees where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.isolated-elements
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.walks-directed-graphs
```

</details>

## Idea

A **directed tree** is a directed graph `G` equipped with a root `r : G` such
that for every vertex `x : G` the type of walks from `x` to `r` is contractible.

## Definition

```agda
is-tree-Directed-Graph-Prop' :
  {l1 l2 : Level} (G : Directed-Graph l1 l2) (r : vertex-Directed-Graph G) →
  Prop (l1 ⊔ l2)
is-tree-Directed-Graph-Prop' G r =
  Π-Prop
    ( vertex-Directed-Graph G)
    ( λ x → is-contr-Prop (walk-Directed-Graph G x r))

is-tree-Directed-Graph' :
  {l1 l2 : Level} (G : Directed-Graph l1 l2) (r : vertex-Directed-Graph G) →
  UU (l1 ⊔ l2)
is-tree-Directed-Graph' G r = type-Prop (is-tree-Directed-Graph-Prop' G r)

is-prop-is-tree-Directed-Graph' :
  {l1 l2 : Level} (G : Directed-Graph l1 l2) (r : vertex-Directed-Graph G) →
  is-prop (is-tree-Directed-Graph' G r)
is-prop-is-tree-Directed-Graph' G r =
  is-prop-type-Prop (is-tree-Directed-Graph-Prop' G r)

is-tree-Directed-Graph :
  {l1 l2 : Level} → Directed-Graph l1 l2 → UU (l1 ⊔ l2)
is-tree-Directed-Graph G =
  Σ ( vertex-Directed-Graph G)
    ( λ r → is-tree-Directed-Graph' G r)

Directed-Tree : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Directed-Tree l1 l2 =
  Σ ( Directed-Graph l1 l2) is-tree-Directed-Graph

module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  graph-Directed-Tree : Directed-Graph l1 l2
  graph-Directed-Tree = pr1 T

  node-Directed-Tree : UU l1
  node-Directed-Tree = vertex-Directed-Graph graph-Directed-Tree

  edge-Directed-Tree : (x y : node-Directed-Tree) → UU l2
  edge-Directed-Tree = edge-Directed-Graph graph-Directed-Tree

  direct-predecessor-Directed-Tree : node-Directed-Tree → UU (l1 ⊔ l2)
  direct-predecessor-Directed-Tree x =
    Σ node-Directed-Tree (λ y → edge-Directed-Tree y x)

  node-direct-predecessor-Directed-Tree :
    (x : node-Directed-Tree) →
    direct-predecessor-Directed-Tree x → node-Directed-Tree
  node-direct-predecessor-Directed-Tree x = pr1

  edge-direct-predecessor-Directed-Tree :
    (x : node-Directed-Tree) (y : direct-predecessor-Directed-Tree x) →
    edge-Directed-Tree (node-direct-predecessor-Directed-Tree x y) x
  edge-direct-predecessor-Directed-Tree x = pr2

  walk-Directed-Tree : (x y : node-Directed-Tree) → UU (l1 ⊔ l2)
  walk-Directed-Tree = walk-Directed-Graph graph-Directed-Tree

  walk-Directed-Tree' : (x y : node-Directed-Tree) → UU (l1 ⊔ l2)
  walk-Directed-Tree' = walk-Directed-Graph' graph-Directed-Tree

  compute-walk-Directed-Tree :
    (x y : node-Directed-Tree) →
    walk-Directed-Tree x y ≃ walk-Directed-Tree' x y
  compute-walk-Directed-Tree =
    compute-walk-Directed-Graph graph-Directed-Tree

  refl-walk-Directed-Tree :
    {x : node-Directed-Tree} → walk-Directed-Tree x x
  refl-walk-Directed-Tree = refl-walk-Directed-Graph

  cons-walk-Directed-Tree :
    {x y z : node-Directed-Tree} (e : edge-Directed-Tree x y) →
    walk-Directed-Tree y z → walk-Directed-Tree x z
  cons-walk-Directed-Tree = cons-walk-Directed-Graph

  unit-walk-Directed-Tree :
    {x y : node-Directed-Tree} →
    edge-Directed-Tree x y → walk-Directed-Tree x y
  unit-walk-Directed-Tree = unit-walk-Directed-Graph graph-Directed-Tree

  length-walk-Directed-Tree :
    {x y : node-Directed-Tree} → walk-Directed-Tree x y → ℕ
  length-walk-Directed-Tree =
    length-walk-Directed-Graph graph-Directed-Tree

  is-tree-Directed-Tree : is-tree-Directed-Graph graph-Directed-Tree
  is-tree-Directed-Tree = pr2 T

  root-Directed-Tree : node-Directed-Tree
  root-Directed-Tree = pr1 is-tree-Directed-Tree

  is-root-Directed-Tree : node-Directed-Tree → UU l1
  is-root-Directed-Tree x = root-Directed-Tree ＝ x

  unique-walk-to-root-Directed-Tree :
    is-tree-Directed-Graph' graph-Directed-Tree root-Directed-Tree
  unique-walk-to-root-Directed-Tree = pr2 is-tree-Directed-Tree

  walk-to-root-Directed-Tree :
    (x : node-Directed-Tree) → walk-Directed-Tree x root-Directed-Tree
  walk-to-root-Directed-Tree x =
    center (unique-walk-to-root-Directed-Tree x)

  unique-walk-to-root-Directed-Tree' :
    (x : node-Directed-Tree) →
    is-contr (walk-Directed-Tree' x root-Directed-Tree)
  unique-walk-to-root-Directed-Tree' x =
    is-contr-equiv'
      ( walk-Directed-Tree x root-Directed-Tree)
      ( compute-walk-Directed-Tree x root-Directed-Tree)
      ( unique-walk-to-root-Directed-Tree x)

  walk-to-root-Directed-Tree' :
    (x : node-Directed-Tree) → walk-Directed-Tree' x root-Directed-Tree
  walk-to-root-Directed-Tree' x =
    center (unique-walk-to-root-Directed-Tree' x)
```

### Proper nodes of directed trees

We define **proper nodes** of a directed tree to be nodes that are distinct from
the root.

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  is-proper-node-Directed-Tree-Prop : node-Directed-Tree T → Prop l1
  is-proper-node-Directed-Tree-Prop x =
    neg-type-Prop (is-root-Directed-Tree T x)

  is-proper-node-Directed-Tree : node-Directed-Tree T → UU l1
  is-proper-node-Directed-Tree x =
    type-Prop (is-proper-node-Directed-Tree-Prop x)

  is-prop-is-proper-node-Directed-Tree :
    (x : node-Directed-Tree T) → is-prop (is-proper-node-Directed-Tree x)
  is-prop-is-proper-node-Directed-Tree x =
    is-prop-type-Prop (is-proper-node-Directed-Tree-Prop x)

  is-proof-irrelevant-is-proper-node-Directed-Tree :
    (x : node-Directed-Tree T) →
    is-proof-irrelevant (is-proper-node-Directed-Tree x)
  is-proof-irrelevant-is-proper-node-Directed-Tree x =
    is-proof-irrelevant-is-prop (is-prop-is-proper-node-Directed-Tree x)

  proper-node-Directed-Tree : UU l1
  proper-node-Directed-Tree =
    Σ (node-Directed-Tree T) is-proper-node-Directed-Tree

  node-proper-node-Directed-Tree :
    proper-node-Directed-Tree → node-Directed-Tree T
  node-proper-node-Directed-Tree = pr1

  is-proper-node-proper-node-Directed-Tree :
    (x : proper-node-Directed-Tree) →
    is-proper-node-Directed-Tree (node-proper-node-Directed-Tree x)
  is-proper-node-proper-node-Directed-Tree = pr2
```

## Properties

### Being a tree is a proposition

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  uniqueness-root-is-tree-Directed-Graph :
    (H K : is-tree-Directed-Graph G) → pr1 H ＝ pr1 K
  uniqueness-root-is-tree-Directed-Graph (r , H) (s , K) =
    eq-is-refl-concat-walk-Directed-Graph G
      ( center (K r))
      ( center (H s))
      ( eq-is-contr (H r))

  is-prop-is-tree-Directed-Graph : is-prop (is-tree-Directed-Graph G)
  is-prop-is-tree-Directed-Graph =
    is-prop-all-elements-equal
      ( λ H K →
        eq-type-subtype
          ( is-tree-Directed-Graph-Prop' G)
          ( uniqueness-root-is-tree-Directed-Graph H K))

  is-tree-directed-graph-Prop : Prop (l1 ⊔ l2)
  pr1 is-tree-directed-graph-Prop = is-tree-Directed-Graph G
  pr2 is-tree-directed-graph-Prop = is-prop-is-tree-Directed-Graph

uniqueness-root-Directed-Tree :
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  (H : is-tree-Directed-Graph (graph-Directed-Tree T)) →
  is-root-Directed-Tree T (pr1 H)
uniqueness-root-Directed-Tree T =
  uniqueness-root-is-tree-Directed-Graph
    ( graph-Directed-Tree T)
    ( is-tree-Directed-Tree T)
```

### The root in a tree is an isolated element

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  abstract
    is-decidable-is-root-walk-Directed-Tree :
      (x : node-Directed-Tree T)
      (w : walk-Directed-Tree T x (root-Directed-Tree T)) →
      is-decidable (is-root-Directed-Tree T x)
    is-decidable-is-root-walk-Directed-Tree ._ refl-walk-Directed-Graph =
      inl refl
    is-decidable-is-root-walk-Directed-Tree x
      ( cons-walk-Directed-Graph {.x} {y} e w) =
      inr
        ( λ where
          refl →
            neq-cons-refl-walk-Directed-Graph
              ( graph-Directed-Tree T)
              ( x)
              ( y)
              ( e)
              ( w)
              ( eq-is-contr (unique-walk-to-root-Directed-Tree T x)))

  is-isolated-root-Directed-Tree : is-isolated (root-Directed-Tree T)
  is-isolated-root-Directed-Tree x =
    is-decidable-is-root-walk-Directed-Tree x (walk-to-root-Directed-Tree T x)

  is-prop-is-root-Directed-Tree :
    (x : node-Directed-Tree T) → is-prop (is-root-Directed-Tree T x)
  is-prop-is-root-Directed-Tree =
    is-prop-eq-isolated-element
      ( root-Directed-Tree T)
      ( is-isolated-root-Directed-Tree)

  is-root-directed-tree-Prop :
    (x : node-Directed-Tree T) → Prop l1
  pr1 (is-root-directed-tree-Prop x) = is-root-Directed-Tree T x
  pr2 (is-root-directed-tree-Prop x) = is-prop-is-root-Directed-Tree x

  is-contr-loop-space-root-Directed-Tree :
    is-contr (root-Directed-Tree T ＝ root-Directed-Tree T)
  is-contr-loop-space-root-Directed-Tree =
    is-contr-loop-space-isolated-element
      ( root-Directed-Tree T)
      ( is-isolated-root-Directed-Tree)

  eq-refl-root-Directed-Tree :
    (p : root-Directed-Tree T ＝ root-Directed-Tree T) → p ＝ refl
  eq-refl-root-Directed-Tree p =
    eq-is-contr is-contr-loop-space-root-Directed-Tree

  eq-refl-root-Directed-Tree' :
    (p : root-Directed-Tree T ＝ root-Directed-Tree T) → refl ＝ p
  eq-refl-root-Directed-Tree' p =
    eq-is-contr is-contr-loop-space-root-Directed-Tree
```

### The root has no direct successors

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  no-direct-successor-root-Directed-Tree :
    ¬ (Σ (node-Directed-Tree T) (edge-Directed-Tree T (root-Directed-Tree T)))
  no-direct-successor-root-Directed-Tree (x , e) =
    neq-cons-refl-walk-Directed-Graph
      ( graph-Directed-Tree T)
      ( root-Directed-Tree T)
      ( x)
      ( e)
      ( walk-to-root-Directed-Tree T x)
      ( eq-is-contr
        ( unique-walk-to-root-Directed-Tree T (root-Directed-Tree T)))

  is-proper-node-direct-successor-Directed-Tree :
    {x y : node-Directed-Tree T} (e : edge-Directed-Tree T x y) →
    ¬ (is-root-Directed-Tree T x)
  is-proper-node-direct-successor-Directed-Tree e refl =
    no-direct-successor-root-Directed-Tree (_ , e)
```

### The type of edges to the root is a proposition

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  is-proof-irrelevant-edge-to-root-Directed-Tree :
    (x : node-Directed-Tree T) →
    is-proof-irrelevant (edge-Directed-Tree T x (root-Directed-Tree T))
  pr1 (is-proof-irrelevant-edge-to-root-Directed-Tree x e) = e
  pr2 (is-proof-irrelevant-edge-to-root-Directed-Tree x e) e' =
    is-injective-unit-walk-Directed-Graph
      ( graph-Directed-Tree T)
      ( eq-is-contr (unique-walk-to-root-Directed-Tree T x))

  is-prop-edge-to-root-Directed-Tree :
    (x : node-Directed-Tree T) →
    is-prop (edge-Directed-Tree T x (root-Directed-Tree T))
  is-prop-edge-to-root-Directed-Tree x =
    is-prop-is-proof-irrelevant
      ( is-proof-irrelevant-edge-to-root-Directed-Tree x)

  eq-edge-to-root-Directed-Tree :
    (x : node-Directed-Tree T)
    (e e' : edge-Directed-Tree T x (root-Directed-Tree T)) → e ＝ e'
  eq-edge-to-root-Directed-Tree x e e' =
    eq-is-prop (is-prop-edge-to-root-Directed-Tree x)
```

### Graphs in which vertices have unique direct-successors are trees if for every vertex `x` there is a walk from `x` to the root

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2) (r : vertex-Directed-Graph G)
  where

  unique-direct-successor-Directed-Graph : UU (l1 ⊔ l2)
  unique-direct-successor-Directed-Graph =
    (x : vertex-Directed-Graph G) →
    is-contr ((r ＝ x) + Σ (vertex-Directed-Graph G) (edge-Directed-Graph G x))

  no-direct-successor-root-unique-direct-successor-Directed-Graph :
    unique-direct-successor-Directed-Graph →
    is-empty (Σ (vertex-Directed-Graph G) (edge-Directed-Graph G r))
  no-direct-successor-root-unique-direct-successor-Directed-Graph H =
    is-empty-right-summand-is-contr-coproduct (H r) refl

  is-isolated-root-unique-direct-successor-Directed-Graph :
    unique-direct-successor-Directed-Graph → is-isolated r
  is-isolated-root-unique-direct-successor-Directed-Graph H x =
    map-coproduct
      ( id)
      ( is-empty-left-summand-is-contr-coproduct (H x))
      ( center (H x))

  is-torsorial-walk-from-root-unique-direct-successor-Directed-Graph :
    unique-direct-successor-Directed-Graph →
    is-torsorial (walk-Directed-Graph G r)
  pr1 (is-torsorial-walk-from-root-unique-direct-successor-Directed-Graph H) =
    ( r , refl-walk-Directed-Graph)
  pr2
    ( is-torsorial-walk-from-root-unique-direct-successor-Directed-Graph H)
    ( y , refl-walk-Directed-Graph) =
    refl
  pr2
    ( is-torsorial-walk-from-root-unique-direct-successor-Directed-Graph H)
    ( y , cons-walk-Directed-Graph e w) =
    ex-falso
      ( no-direct-successor-root-unique-direct-successor-Directed-Graph H
        ( _ , e))

  is-contr-loop-space-root-unique-direct-successor-Directed-Graph :
    unique-direct-successor-Directed-Graph → is-contr (r ＝ r)
  is-contr-loop-space-root-unique-direct-successor-Directed-Graph H =
    is-contr-loop-space-isolated-element r
      ( is-isolated-root-unique-direct-successor-Directed-Graph H)

  is-not-root-has-unique-direct-successor-Directed-Graph :
    (x : vertex-Directed-Graph G) →
    is-contr
      ( (r ＝ x) + Σ (vertex-Directed-Graph G) (edge-Directed-Graph G x)) →
    Σ (vertex-Directed-Graph G) (edge-Directed-Graph G x) → r ≠ x
  is-not-root-has-unique-direct-successor-Directed-Graph x H (y , e) =
    is-empty-left-summand-is-contr-coproduct H (y , e)

  is-proof-irrelevant-direct-successor-has-unique-direct-successor-Directed-Graph :
    (x : vertex-Directed-Graph G) →
    is-contr
      ( (r ＝ x) + Σ (vertex-Directed-Graph G) (edge-Directed-Graph G x)) →
    is-proof-irrelevant (Σ (vertex-Directed-Graph G) (edge-Directed-Graph G x))
  is-proof-irrelevant-direct-successor-has-unique-direct-successor-Directed-Graph
    x H (y , e) =
    is-contr-right-summand H (y , e)

  is-proof-irrelevant-walk-unique-direct-successor-Directed-Graph :
    unique-direct-successor-Directed-Graph → (x : vertex-Directed-Graph G) →
    is-proof-irrelevant (walk-Directed-Graph G x r)
  pr1
    ( is-proof-irrelevant-walk-unique-direct-successor-Directed-Graph H x
      refl-walk-Directed-Graph) =
    refl-walk-Directed-Graph
  pr2
    ( is-proof-irrelevant-walk-unique-direct-successor-Directed-Graph H x
      refl-walk-Directed-Graph)
    ( w) =
    ( inv
      ( ap
        ( λ α → tr (walk-Directed-Graph G x) α refl-walk-Directed-Graph)
        ( eq-is-contr
          ( is-contr-loop-space-root-unique-direct-successor-Directed-Graph
            ( H))))) ∙
    ( pr2
      ( pair-eq-Σ
        ( eq-is-contr
          ( is-torsorial-walk-from-root-unique-direct-successor-Directed-Graph
            H)
          { (r , refl-walk-Directed-Graph)}
          { (r , w)})))
  is-proof-irrelevant-walk-unique-direct-successor-Directed-Graph H x
    ( cons-walk-Directed-Graph {.x} {y} e w) =
    is-contr-equiv
      ( walk-Directed-Graph G y r)
      ( equivalence-reasoning
        walk-Directed-Graph G x r
        ≃ coproduct-walk-Directed-Graph G x r
          by compute-coproduct-walk-Directed-Graph G x r
        ≃ Σ ( vertex-Directed-Graph G)
            ( λ y → edge-Directed-Graph G x y × walk-Directed-Graph G y r)
          by
          left-unit-law-coproduct-is-empty
            ( r ＝ x)
            ( Σ ( vertex-Directed-Graph G)
                ( λ y →
                  edge-Directed-Graph G x y × walk-Directed-Graph G y r))
            ( is-not-root-has-unique-direct-successor-Directed-Graph x
              ( H x)
              ( y , e))
        ≃ Σ ( Σ (vertex-Directed-Graph G) (edge-Directed-Graph G x))
            ( λ p → walk-Directed-Graph G (pr1 p) r)
          by inv-associative-Σ
        ≃ walk-Directed-Graph G y r
          by
          left-unit-law-Σ-is-contr
            ( is-proof-irrelevant-direct-successor-has-unique-direct-successor-Directed-Graph
              ( x)
              ( H x)
              ( y , e))
            (y , e))
      ( is-proof-irrelevant-walk-unique-direct-successor-Directed-Graph H y w)

  is-tree-unique-direct-successor-Directed-Graph' :
    unique-direct-successor-Directed-Graph →
    ((x : vertex-Directed-Graph G) → walk-Directed-Graph G x r) →
    is-tree-Directed-Graph' G r
  is-tree-unique-direct-successor-Directed-Graph' H w x =
    is-proof-irrelevant-walk-unique-direct-successor-Directed-Graph H x (w x)

  is-tree-unique-direct-successor-Directed-Graph :
    unique-direct-successor-Directed-Graph →
    ((x : vertex-Directed-Graph G) → walk-Directed-Graph G x r) →
    is-tree-Directed-Graph G
  pr1 (is-tree-unique-direct-successor-Directed-Graph H w) = r
  pr2 (is-tree-unique-direct-successor-Directed-Graph H w) =
    is-tree-unique-direct-successor-Directed-Graph' H w
```

### Nodes in trees have unique direct-successors

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  center-walk-unique-direct-successor-Directed-Tree :
    (x : node-Directed-Tree T)
    (w : walk-Directed-Tree T x (root-Directed-Tree T)) →
    is-root-Directed-Tree T x +
    Σ (node-Directed-Tree T) (edge-Directed-Tree T x)
  center-walk-unique-direct-successor-Directed-Tree .(root-Directed-Tree T)
    refl-walk-Directed-Graph =
    inl refl
  center-walk-unique-direct-successor-Directed-Tree x
    ( cons-walk-Directed-Graph {.x} {y} e w) =
    inr (y , e)

  center-unique-direct-successor-Directed-Tree :
    (x : node-Directed-Tree T) →
    is-root-Directed-Tree T x +
    Σ (node-Directed-Tree T) (edge-Directed-Tree T x)
  center-unique-direct-successor-Directed-Tree x =
    center-walk-unique-direct-successor-Directed-Tree x
      ( walk-to-root-Directed-Tree T x)

  contraction-walk-unique-direct-successor-Directed-Tree :
    ( x : node-Directed-Tree T)
    ( w : walk-Directed-Tree T x (root-Directed-Tree T)) →
    ( p :
      is-root-Directed-Tree T x +
      Σ (node-Directed-Tree T) (edge-Directed-Tree T x)) →
    center-walk-unique-direct-successor-Directed-Tree x w ＝ p
  contraction-walk-unique-direct-successor-Directed-Tree ._
    ( refl-walk-Directed-Graph)
    ( inl p) =
    ap inl (eq-refl-root-Directed-Tree' T p)
  contraction-walk-unique-direct-successor-Directed-Tree ._
    ( refl-walk-Directed-Graph)
    ( inr (y , e)) =
    ex-falso (no-direct-successor-root-Directed-Tree T (y , e))
  contraction-walk-unique-direct-successor-Directed-Tree _
    ( cons-walk-Directed-Graph {._} {y} e w)
    ( inl refl) =
    ex-falso (no-direct-successor-root-Directed-Tree T (y , e))
  contraction-walk-unique-direct-successor-Directed-Tree _
    ( cons-walk-Directed-Graph {x} {y} e w)
    ( inr (z , f)) =
    ap
      ( inr)
      ( eq-direct-successor-eq-cons-walk-Directed-Graph
        ( graph-Directed-Tree T)
        ( x)
        ( e)
        ( f)
        ( walk-to-root-Directed-Tree T y)
        ( walk-to-root-Directed-Tree T z)
        ( eq-is-contr (unique-walk-to-root-Directed-Tree T x)))

  contraction-unique-direct-successor-Directed-Tree :
    ( x : node-Directed-Tree T) →
    ( p :
      is-root-Directed-Tree T x +
      Σ (node-Directed-Tree T) (edge-Directed-Tree T x)) →
    center-unique-direct-successor-Directed-Tree x ＝ p
  contraction-unique-direct-successor-Directed-Tree x =
    contraction-walk-unique-direct-successor-Directed-Tree x
      ( walk-to-root-Directed-Tree T x)

  unique-direct-successor-Directed-Tree :
    unique-direct-successor-Directed-Graph
      ( graph-Directed-Tree T)
      ( root-Directed-Tree T)
  pr1 (unique-direct-successor-Directed-Tree x) =
    center-unique-direct-successor-Directed-Tree x
  pr2 (unique-direct-successor-Directed-Tree x) =
    contraction-unique-direct-successor-Directed-Tree x

  unique-direct-successor-is-proper-node-Directed-Tree :
    (x : node-Directed-Tree T) → is-proper-node-Directed-Tree T x →
    is-contr (Σ (node-Directed-Tree T) (edge-Directed-Tree T x))
  unique-direct-successor-is-proper-node-Directed-Tree x f =
    is-contr-equiv'
      ( ( is-root-Directed-Tree T x) +
        ( Σ (node-Directed-Tree T) (edge-Directed-Tree T x)))
      ( left-unit-law-coproduct-is-empty
        ( is-root-Directed-Tree T x)
        ( Σ (node-Directed-Tree T) (edge-Directed-Tree T x))
        ( f))
      ( unique-direct-successor-Directed-Tree x)

  abstract
    is-proof-irrelevant-direct-successor-Directed-Tree :
      (x : node-Directed-Tree T) →
      is-proof-irrelevant (Σ (node-Directed-Tree T) (edge-Directed-Tree T x))
    is-proof-irrelevant-direct-successor-Directed-Tree x (y , e) =
      unique-direct-successor-is-proper-node-Directed-Tree x
        ( λ where refl → no-direct-successor-root-Directed-Tree T (y , e))

  is-prop-direct-successor-Directed-Tree :
    (x : node-Directed-Tree T) →
    is-prop (Σ (node-Directed-Tree T) (edge-Directed-Tree T x))
  is-prop-direct-successor-Directed-Tree x =
    is-prop-is-proof-irrelevant
      ( is-proof-irrelevant-direct-successor-Directed-Tree x)

  eq-direct-successor-Directed-Tree :
    {x : node-Directed-Tree T}
    (u v : Σ (node-Directed-Tree T) (edge-Directed-Tree T x)) → u ＝ v
  eq-direct-successor-Directed-Tree {x} =
    eq-is-prop' (is-prop-direct-successor-Directed-Tree x)

  direct-successor-is-proper-node-Directed-Tree :
    (x : node-Directed-Tree T) → is-proper-node-Directed-Tree T x →
    Σ (node-Directed-Tree T) (edge-Directed-Tree T x)
  direct-successor-is-proper-node-Directed-Tree x f =
    center (unique-direct-successor-is-proper-node-Directed-Tree x f)
```

### Transporting walks in directed trees

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  tr-walk-eq-direct-successor-Directed-Tree :
    {x y : node-Directed-Tree T}
    (u v : Σ (node-Directed-Tree T) (edge-Directed-Tree T x)) →
    walk-Directed-Tree T (pr1 u) y → walk-Directed-Tree T (pr1 v) y
  tr-walk-eq-direct-successor-Directed-Tree {x} {y} u v =
    tr
      ( λ r → walk-Directed-Tree T (pr1 r) y)
      ( eq-direct-successor-Directed-Tree T u v)

  eq-tr-walk-eq-direct-successor-Directed-Tree' :
    {x y : node-Directed-Tree T}
    (u v : Σ (node-Directed-Tree T) (edge-Directed-Tree T x)) →
    (w : walk-Directed-Tree T (pr1 u) y) →
    (p : u ＝ v) →
    cons-walk-Directed-Graph
      ( pr2 v)
      ( tr (λ r → walk-Directed-Tree T (pr1 r) y) p w) ＝
    cons-walk-Directed-Graph (pr2 u) w
  eq-tr-walk-eq-direct-successor-Directed-Tree' u .u w refl = refl

  eq-tr-walk-eq-direct-successor-Directed-Tree :
    {x y : node-Directed-Tree T}
    (u v : Σ (node-Directed-Tree T) (edge-Directed-Tree T x)) →
    (w : walk-Directed-Tree T (pr1 u) y) →
    cons-walk-Directed-Graph
      ( pr2 v)
      ( tr-walk-eq-direct-successor-Directed-Tree u v w) ＝
    cons-walk-Directed-Graph (pr2 u) w
  eq-tr-walk-eq-direct-successor-Directed-Tree u v w =
    eq-tr-walk-eq-direct-successor-Directed-Tree' u v w
      ( eq-direct-successor-Directed-Tree T u v)
```

## See also

There are many variations of the notion of trees, all of which are subtly
different:

- Undirected trees can be found in
  [`trees.undirected-trees`](trees.undirected-trees.md).
- Acyclic undirected graphs can be found in
  [`graph-theory.acyclic-undirected-graphs`](graph-theory.acyclic-undirected-graphs.md).
