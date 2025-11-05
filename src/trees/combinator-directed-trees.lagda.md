# The combinator of directed trees

```agda
module trees.combinator-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.isolated-elements
open import foundation.maybe
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.morphisms-directed-graphs
open import graph-theory.walks-directed-graphs

open import trees.bases-directed-trees
open import trees.directed-trees
open import trees.equivalences-directed-trees
open import trees.fibers-directed-trees
open import trees.morphisms-directed-trees
```

</details>

## Idea

The
{{#concept "combinator operation" Disambiguation="on directed trees" Agda=combinator-Directed-Tree}}
on [directed trees](trees.directed-trees.md) combines a family of directed trees
into a single directed tree with a new root.

## Definitions

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (T : I → Directed-Tree l2 l3)
  where

  data node-combinator-Directed-Tree : UU (l1 ⊔ l2) where
    root-combinator-Directed-Tree : node-combinator-Directed-Tree
    node-inclusion-combinator-Directed-Tree :
      (i : I) → node-Directed-Tree (T i) → node-combinator-Directed-Tree

  data
    edge-combinator-Directed-Tree :
      ( x y : node-combinator-Directed-Tree) → UU (l1 ⊔ l2 ⊔ l3) where
    edge-to-root-combinator-Directed-Tree :
      (i : I) →
      edge-combinator-Directed-Tree
        ( node-inclusion-combinator-Directed-Tree i (root-Directed-Tree (T i)))
        ( root-combinator-Directed-Tree)
    edge-inclusion-combinator-Directed-Tree :
      (i : I) (x y : node-Directed-Tree (T i)) →
      edge-Directed-Tree (T i) x y →
      edge-combinator-Directed-Tree
        ( node-inclusion-combinator-Directed-Tree i x)
        ( node-inclusion-combinator-Directed-Tree i y)

  graph-combinator-Directed-Tree : Directed-Graph (l1 ⊔ l2) (l1 ⊔ l2 ⊔ l3)
  pr1 graph-combinator-Directed-Tree = node-combinator-Directed-Tree
  pr2 graph-combinator-Directed-Tree = edge-combinator-Directed-Tree

  inclusion-combinator-Directed-Tree :
    (i : I) →
    hom-Directed-Graph
      ( graph-Directed-Tree (T i))
      ( graph-combinator-Directed-Tree)
  pr1 (inclusion-combinator-Directed-Tree i) =
    node-inclusion-combinator-Directed-Tree i
  pr2 (inclusion-combinator-Directed-Tree i) =
    edge-inclusion-combinator-Directed-Tree i

  walk-combinator-Directed-Tree :
    ( x y : node-combinator-Directed-Tree) → UU (l1 ⊔ l2 ⊔ l3)
  walk-combinator-Directed-Tree =
    walk-Directed-Graph graph-combinator-Directed-Tree

  walk-inclusion-combinator-Directed-Tree :
    (i : I) (x y : node-Directed-Tree (T i)) →
    walk-Directed-Graph (graph-Directed-Tree (T i)) x y →
    walk-combinator-Directed-Tree
      ( node-inclusion-combinator-Directed-Tree i x)
      ( node-inclusion-combinator-Directed-Tree i y)
  walk-inclusion-combinator-Directed-Tree a x y =
    walk-hom-Directed-Graph
      ( graph-Directed-Tree (T a))
      ( graph-combinator-Directed-Tree)
      ( inclusion-combinator-Directed-Tree a)

  walk-to-root-combinator-Directed-Tree :
    ( x : node-combinator-Directed-Tree) →
    walk-combinator-Directed-Tree x root-combinator-Directed-Tree
  walk-to-root-combinator-Directed-Tree root-combinator-Directed-Tree =
    refl-walk-Directed-Graph
  walk-to-root-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x) =
    snoc-walk-Directed-Graph
      ( graph-combinator-Directed-Tree)
      ( walk-inclusion-combinator-Directed-Tree i x
        ( root-Directed-Tree (T i))
        ( walk-to-root-Directed-Tree (T i) x))
      ( edge-to-root-combinator-Directed-Tree i)

  is-root-combinator-Directed-Tree :
    node-combinator-Directed-Tree → UU (l1 ⊔ l2)
  is-root-combinator-Directed-Tree x = root-combinator-Directed-Tree ＝ x

  is-isolated-root-combinator-Directed-Tree :
    is-isolated root-combinator-Directed-Tree
  is-isolated-root-combinator-Directed-Tree root-combinator-Directed-Tree =
    inl refl
  is-isolated-root-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x) =
    inr (λ ())

  cases-center-unique-direct-successor-combinator-Directed-Tree' :
    (i : I) (x : node-Directed-Tree (T i)) →
    is-decidable (is-root-Directed-Tree (T i) x) →
    Σ ( node-combinator-Directed-Tree)
      ( edge-combinator-Directed-Tree
        ( node-inclusion-combinator-Directed-Tree i x))
  cases-center-unique-direct-successor-combinator-Directed-Tree' a ._
    ( inl refl) =
    ( root-combinator-Directed-Tree , edge-to-root-combinator-Directed-Tree a)
  cases-center-unique-direct-successor-combinator-Directed-Tree' i x (inr f) =
    map-Σ
      ( edge-combinator-Directed-Tree
        ( node-inclusion-combinator-Directed-Tree i x))
      ( node-inclusion-combinator-Directed-Tree i)
      ( edge-inclusion-combinator-Directed-Tree i x)
      ( direct-successor-is-proper-node-Directed-Tree (T i) x f)

  center-unique-direct-successor-combinator-Directed-Tree' :
    ( x : node-combinator-Directed-Tree) →
    ¬ (is-root-combinator-Directed-Tree x) →
    Σ node-combinator-Directed-Tree (edge-combinator-Directed-Tree x)
  center-unique-direct-successor-combinator-Directed-Tree'
    root-combinator-Directed-Tree f = ex-falso (f refl)
  center-unique-direct-successor-combinator-Directed-Tree'
    ( node-inclusion-combinator-Directed-Tree i x) f =
    cases-center-unique-direct-successor-combinator-Directed-Tree' i x
      ( is-isolated-root-Directed-Tree (T i) x)

  cases-center-unique-direct-successor-combinator-Directed-Tree :
    (i : I) (x : node-Directed-Tree (T i)) →
    is-decidable (is-root-Directed-Tree (T i) x) →
    Σ ( node-combinator-Directed-Tree)
      ( edge-combinator-Directed-Tree
        ( node-inclusion-combinator-Directed-Tree i x))
  cases-center-unique-direct-successor-combinator-Directed-Tree i ._
    ( inl refl) =
    root-combinator-Directed-Tree ,
    edge-to-root-combinator-Directed-Tree i
  cases-center-unique-direct-successor-combinator-Directed-Tree i x (inr f) =
    map-Σ
      ( edge-combinator-Directed-Tree
        ( node-inclusion-combinator-Directed-Tree i x))
      ( node-inclusion-combinator-Directed-Tree i)
      ( edge-inclusion-combinator-Directed-Tree i x)
      ( direct-successor-is-proper-node-Directed-Tree (T i) x f)

  center-unique-direct-successor-combinator-Directed-Tree :
    (x : node-combinator-Directed-Tree) →
    is-root-combinator-Directed-Tree x +
    Σ node-combinator-Directed-Tree (edge-combinator-Directed-Tree x)
  center-unique-direct-successor-combinator-Directed-Tree
    root-combinator-Directed-Tree =
    inl refl
  center-unique-direct-successor-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x) =
    inr
      ( cases-center-unique-direct-successor-combinator-Directed-Tree i x
        ( is-isolated-root-Directed-Tree (T i) x))

  cases-contraction-unique-direct-successor-combinator-Directed-Tree :
    (i : I) (x : node-Directed-Tree (T i)) →
    (d : is-decidable (is-root-Directed-Tree (T i) x)) →
    ( p :
      Σ ( node-combinator-Directed-Tree)
        ( edge-combinator-Directed-Tree
          ( node-inclusion-combinator-Directed-Tree i x))) →
    cases-center-unique-direct-successor-combinator-Directed-Tree i x d ＝ p
  cases-contraction-unique-direct-successor-combinator-Directed-Tree i ._
    ( inl r)
    ( ._ , edge-to-root-combinator-Directed-Tree .i) =
    ap
      ( λ u →
        cases-center-unique-direct-successor-combinator-Directed-Tree i
          ( root-Directed-Tree (T i))
          ( inl u))
      ( eq-refl-root-Directed-Tree (T i) r)
  cases-contraction-unique-direct-successor-combinator-Directed-Tree i ._
    ( inr f)
    ( ._ , edge-to-root-combinator-Directed-Tree .i) =
    ex-falso (f refl)
  cases-contraction-unique-direct-successor-combinator-Directed-Tree i ._
    ( inl refl)
    ( ._ , edge-inclusion-combinator-Directed-Tree .i ._ y e) =
    ex-falso (no-direct-successor-root-Directed-Tree (T i) (y , e))
  cases-contraction-unique-direct-successor-combinator-Directed-Tree i x
    ( inr f)
    ( ._ , edge-inclusion-combinator-Directed-Tree .i .x y e) =
    ap
      ( map-Σ
        ( edge-combinator-Directed-Tree
          ( node-inclusion-combinator-Directed-Tree i x))
        ( node-inclusion-combinator-Directed-Tree i)
        ( edge-inclusion-combinator-Directed-Tree i x))
      ( eq-is-contr
        ( unique-direct-successor-is-proper-node-Directed-Tree (T i) x f))

  contraction-unique-direct-successor-combinator-Directed-Tree :
    ( x : node-combinator-Directed-Tree) →
    ( p :
      is-root-combinator-Directed-Tree x +
      Σ node-combinator-Directed-Tree (edge-combinator-Directed-Tree x)) →
    center-unique-direct-successor-combinator-Directed-Tree x ＝ p
  contraction-unique-direct-successor-combinator-Directed-Tree ._ (inl refl) =
    refl
  contraction-unique-direct-successor-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x)
    ( inr (y , e)) =
    ap
      ( inr)
      ( cases-contraction-unique-direct-successor-combinator-Directed-Tree i x
        ( is-isolated-root-Directed-Tree (T i) x)
        ( y , e))

  unique-direct-successor-combinator-Directed-Tree :
    unique-direct-successor-Directed-Graph
      ( graph-combinator-Directed-Tree)
      ( root-combinator-Directed-Tree)
  pr1 (unique-direct-successor-combinator-Directed-Tree x) =
    center-unique-direct-successor-combinator-Directed-Tree x
  pr2 (unique-direct-successor-combinator-Directed-Tree x) =
    contraction-unique-direct-successor-combinator-Directed-Tree x

  is-tree-combinator-Directed-Tree :
    is-tree-Directed-Graph graph-combinator-Directed-Tree
  is-tree-combinator-Directed-Tree =
    is-tree-unique-direct-successor-Directed-Graph
      graph-combinator-Directed-Tree
      root-combinator-Directed-Tree
      unique-direct-successor-combinator-Directed-Tree
      walk-to-root-combinator-Directed-Tree

  combinator-Directed-Tree : Directed-Tree (l1 ⊔ l2) (l1 ⊔ l2 ⊔ l3)
  pr1 combinator-Directed-Tree = graph-combinator-Directed-Tree
  pr2 combinator-Directed-Tree = is-tree-combinator-Directed-Tree

  base-combinator-Directed-Tree : UU (l1 ⊔ l2 ⊔ l3)
  base-combinator-Directed-Tree = base-Directed-Tree combinator-Directed-Tree

  is-proper-node-combinator-Directed-Tree :
    node-combinator-Directed-Tree → UU (l1 ⊔ l2)
  is-proper-node-combinator-Directed-Tree =
    is-proper-node-Directed-Tree combinator-Directed-Tree

  proper-node-combinator-Directed-Tree : UU (l1 ⊔ l2)
  proper-node-combinator-Directed-Tree =
    proper-node-Directed-Tree combinator-Directed-Tree

  is-proper-node-inclusion-combinator-Directed-Tree :
    {i : I} {x : node-Directed-Tree (T i)} →
    is-proper-node-combinator-Directed-Tree
      ( node-inclusion-combinator-Directed-Tree i x)
  is-proper-node-inclusion-combinator-Directed-Tree {i} {x} ()
```

## Properties

### The type of direct predecessors of `x : T i` is equivalent to the type of direct predecessors of the inclusion of `x` in `combinator T`

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (T : I → Directed-Tree l2 l3)
  (i : I) (x : node-Directed-Tree (T i))
  where

  direct-predecessor-combinator-Directed-Tree : UU (l1 ⊔ l2 ⊔ l3)
  direct-predecessor-combinator-Directed-Tree =
    Σ ( node-combinator-Directed-Tree T)
      ( λ y →
        edge-combinator-Directed-Tree T y
          ( node-inclusion-combinator-Directed-Tree i x))

  map-compute-direct-predecessor-combinator-Directed-Tree :
    direct-predecessor-Directed-Tree (T i) x →
    direct-predecessor-combinator-Directed-Tree
  pr1 (map-compute-direct-predecessor-combinator-Directed-Tree (y , e)) =
    node-inclusion-combinator-Directed-Tree i y
  pr2 (map-compute-direct-predecessor-combinator-Directed-Tree (y , e)) =
    edge-inclusion-combinator-Directed-Tree i y x e

  map-inv-compute-direct-predecessor-combinator-Directed-Tree :
    direct-predecessor-combinator-Directed-Tree →
    direct-predecessor-Directed-Tree (T i) x
  map-inv-compute-direct-predecessor-combinator-Directed-Tree
    ( ._ , edge-inclusion-combinator-Directed-Tree .i y .x e) =
    ( y , e)

  is-section-map-inv-compute-direct-predecessor-combinator-Directed-Tree :
    ( map-compute-direct-predecessor-combinator-Directed-Tree ∘
      map-inv-compute-direct-predecessor-combinator-Directed-Tree) ~ id
  is-section-map-inv-compute-direct-predecessor-combinator-Directed-Tree
    ( ._ , edge-inclusion-combinator-Directed-Tree .i y .x e) =
    refl

  is-retraction-map-inv-compute-direct-predecessor-combinator-Directed-Tree :
    ( map-inv-compute-direct-predecessor-combinator-Directed-Tree ∘
      map-compute-direct-predecessor-combinator-Directed-Tree) ~ id
  is-retraction-map-inv-compute-direct-predecessor-combinator-Directed-Tree
    ( y , e) =
    refl

  is-equiv-map-compute-direct-predecessor-combinator-Directed-Tree :
    is-equiv map-compute-direct-predecessor-combinator-Directed-Tree
  is-equiv-map-compute-direct-predecessor-combinator-Directed-Tree =
    is-equiv-is-invertible
      map-inv-compute-direct-predecessor-combinator-Directed-Tree
      is-section-map-inv-compute-direct-predecessor-combinator-Directed-Tree
      is-retraction-map-inv-compute-direct-predecessor-combinator-Directed-Tree

  compute-direct-predecessor-combinator-Directed-Tree :
    direct-predecessor-Directed-Tree (T i) x ≃
    direct-predecessor-combinator-Directed-Tree
  pr1 compute-direct-predecessor-combinator-Directed-Tree =
    map-compute-direct-predecessor-combinator-Directed-Tree
  pr2 compute-direct-predecessor-combinator-Directed-Tree =
    is-equiv-map-compute-direct-predecessor-combinator-Directed-Tree
```

### If `e` is an edge from `node-inclusion i x` to `node-inclusion j y`, then `i ＝ j`

```agda
eq-index-edge-combinator-Directed-Tree :
  {l1 l2 l3 : Level} {I : UU l1} (T : I → Directed-Tree l2 l3)
  {i : I} (x : node-Directed-Tree (T i))
  {j : I} (y : node-Directed-Tree (T j)) →
  edge-combinator-Directed-Tree T
    ( node-inclusion-combinator-Directed-Tree i x)
    ( node-inclusion-combinator-Directed-Tree j y) →
  i ＝ j
eq-index-edge-combinator-Directed-Tree T x y
  ( edge-inclusion-combinator-Directed-Tree _ .x .y e) = refl
```

### The base of the combinator tree of a family `T` of directed tree indexed by `I` is equivalent to `I`

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (T : I → Directed-Tree l2 l3)
  where

  node-base-index-combinator-Directed-Tree :
    I → node-combinator-Directed-Tree T
  node-base-index-combinator-Directed-Tree i =
    node-inclusion-combinator-Directed-Tree i (root-Directed-Tree (T i))

  edge-base-index-combinator-Directed-Tree :
    (i : I) →
    edge-combinator-Directed-Tree T
      ( node-base-index-combinator-Directed-Tree i)
      ( root-combinator-Directed-Tree)
  edge-base-index-combinator-Directed-Tree i =
    edge-to-root-combinator-Directed-Tree i

  base-index-combinator-Directed-Tree :
    I → base-combinator-Directed-Tree T
  pr1 (base-index-combinator-Directed-Tree i) =
    node-base-index-combinator-Directed-Tree i
  pr2 (base-index-combinator-Directed-Tree i) =
    edge-base-index-combinator-Directed-Tree i

  index-base-combinator-Directed-Tree :
    base-combinator-Directed-Tree T → I
  index-base-combinator-Directed-Tree
    ( ._ , edge-to-root-combinator-Directed-Tree i) =
    i

  is-section-index-base-combinator-Directed-Tree :
    ( base-index-combinator-Directed-Tree ∘
      index-base-combinator-Directed-Tree) ~ id
  is-section-index-base-combinator-Directed-Tree
    ( ._ , edge-to-root-combinator-Directed-Tree i) =
    refl

  is-retraction-index-base-combinator-Directed-Tree :
    ( index-base-combinator-Directed-Tree ∘
      base-index-combinator-Directed-Tree) ~ id
  is-retraction-index-base-combinator-Directed-Tree i = refl

  is-equiv-base-index-combinator-Directed-Tree :
    is-equiv base-index-combinator-Directed-Tree
  is-equiv-base-index-combinator-Directed-Tree =
    is-equiv-is-invertible
      index-base-combinator-Directed-Tree
      is-section-index-base-combinator-Directed-Tree
      is-retraction-index-base-combinator-Directed-Tree

  equiv-base-index-combinator-Directed-Tree :
    I ≃ base-combinator-Directed-Tree T
  pr1 equiv-base-index-combinator-Directed-Tree =
    base-index-combinator-Directed-Tree
  pr2 equiv-base-index-combinator-Directed-Tree =
    is-equiv-base-index-combinator-Directed-Tree
```

### The type of nodes of the combinator tree of `T` is equivalent to the dependent sum of the types of nodes of each `T i`, plus a root

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (T : I → Directed-Tree l2 l3)
  where

  map-compute-node-combinator-Directed-Tree :
    Maybe (Σ I (node-Directed-Tree ∘ T)) →
    node-combinator-Directed-Tree T
  map-compute-node-combinator-Directed-Tree (inl (i , x)) =
    node-inclusion-combinator-Directed-Tree i x
  map-compute-node-combinator-Directed-Tree (inr _) =
    root-combinator-Directed-Tree

  map-inv-compute-node-combinator-Directed-Tree :
    node-combinator-Directed-Tree T →
    Maybe (Σ I (node-Directed-Tree ∘ T))
  map-inv-compute-node-combinator-Directed-Tree root-combinator-Directed-Tree =
    exception-Maybe
  map-inv-compute-node-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x) =
    unit-Maybe (i , x)

  is-section-map-inv-compute-node-combinator-Directed-Tree :
    ( map-compute-node-combinator-Directed-Tree ∘
      map-inv-compute-node-combinator-Directed-Tree) ~ id
  is-section-map-inv-compute-node-combinator-Directed-Tree
    root-combinator-Directed-Tree =
    refl
  is-section-map-inv-compute-node-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x) =
    refl

  is-retraction-map-inv-compute-node-combinator-Directed-Tree :
    ( map-inv-compute-node-combinator-Directed-Tree ∘
      map-compute-node-combinator-Directed-Tree) ~ id
  is-retraction-map-inv-compute-node-combinator-Directed-Tree (inl (i , x)) =
    refl
  is-retraction-map-inv-compute-node-combinator-Directed-Tree (inr _) = refl

  is-equiv-map-compute-node-combinator-Directed-Tree :
    is-equiv map-compute-node-combinator-Directed-Tree
  is-equiv-map-compute-node-combinator-Directed-Tree =
    is-equiv-is-invertible
      map-inv-compute-node-combinator-Directed-Tree
      is-section-map-inv-compute-node-combinator-Directed-Tree
      is-retraction-map-inv-compute-node-combinator-Directed-Tree

  compute-node-combinator-Directed-Tree :
    Maybe (Σ I (node-Directed-Tree ∘ T)) ≃ node-combinator-Directed-Tree T
  pr1 compute-node-combinator-Directed-Tree =
    map-compute-node-combinator-Directed-Tree
  pr2 compute-node-combinator-Directed-Tree =
    is-equiv-map-compute-node-combinator-Directed-Tree
```

### The type of proper nodes of the combinator tree of `T` is equivalent to the dependent sum of the types of nodes of each `T i`

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (T : I → Directed-Tree l2 l3)
  where

  map-compute-proper-node-combinator-Directed-Tree :
    Σ I (node-Directed-Tree ∘ T) →
    proper-node-combinator-Directed-Tree T
  map-compute-proper-node-combinator-Directed-Tree (i , x) =
    ( node-inclusion-combinator-Directed-Tree i x ,
      is-proper-node-inclusion-combinator-Directed-Tree T)

  map-inv-compute-proper-node-combinator-Directed-Tree :
    proper-node-combinator-Directed-Tree T →
    Σ I (node-Directed-Tree ∘ T)
  map-inv-compute-proper-node-combinator-Directed-Tree
    ( root-combinator-Directed-Tree , H) =
    ex-falso (H refl)
  map-inv-compute-proper-node-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x , H) = (i , x)

  is-section-map-inv-compute-proper-node-combinator-Directed-Tree :
    ( map-compute-proper-node-combinator-Directed-Tree ∘
      map-inv-compute-proper-node-combinator-Directed-Tree) ~ id
  is-section-map-inv-compute-proper-node-combinator-Directed-Tree
    ( root-combinator-Directed-Tree , H) =
    ex-falso (H refl)
  is-section-map-inv-compute-proper-node-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x , H) =
    eq-pair-eq-fiber
      ( eq-is-prop
        ( is-prop-is-proper-node-Directed-Tree
          ( combinator-Directed-Tree T)
          ( node-inclusion-combinator-Directed-Tree i x)))

  is-retraction-map-inv-compute-proper-node-combinator-Directed-Tree :
    ( map-inv-compute-proper-node-combinator-Directed-Tree ∘
      map-compute-proper-node-combinator-Directed-Tree) ~ id
  is-retraction-map-inv-compute-proper-node-combinator-Directed-Tree (i , x) =
    refl

  is-equiv-map-compute-proper-node-combinator-Directed-Tree :
    is-equiv map-compute-proper-node-combinator-Directed-Tree
  is-equiv-map-compute-proper-node-combinator-Directed-Tree =
    is-equiv-is-invertible
      map-inv-compute-proper-node-combinator-Directed-Tree
      is-section-map-inv-compute-proper-node-combinator-Directed-Tree
      is-retraction-map-inv-compute-proper-node-combinator-Directed-Tree

  compute-proper-node-combinator-Directed-Tree :
    Σ I (node-Directed-Tree ∘ T) ≃ proper-node-combinator-Directed-Tree T
  pr1 compute-proper-node-combinator-Directed-Tree =
    map-compute-proper-node-combinator-Directed-Tree
  pr2 compute-proper-node-combinator-Directed-Tree =
    is-equiv-map-compute-proper-node-combinator-Directed-Tree
```

### The fibers at a base element `b` of the comibinator of a family `T` of trees is equivalent to `T (index-base b)`

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (T : I → Directed-Tree l2 l3)
  where

  node-fiber-combinator-Directed-Tree :
    (i : I) →
    node-Directed-Tree (T i) →
    node-fiber-Directed-Tree
      ( combinator-Directed-Tree T)
      ( node-base-index-combinator-Directed-Tree T i)
  pr1 (node-fiber-combinator-Directed-Tree i x) =
    node-inclusion-combinator-Directed-Tree i x
  pr2 (node-fiber-combinator-Directed-Tree i x) =
    walk-inclusion-combinator-Directed-Tree T i x
      ( root-Directed-Tree (T i))
      ( walk-to-root-Directed-Tree (T i) x)

  compute-map-Σ-node-fiber-combinator-Directed-Tree :
    ( map-Σ
      ( λ b →
        Σ ( node-combinator-Directed-Tree T)
          ( λ x →
            walk-combinator-Directed-Tree T x
              ( node-base-Directed-Tree (combinator-Directed-Tree T) b)))
      ( base-index-combinator-Directed-Tree T)
      ( node-fiber-combinator-Directed-Tree)) ~
    map-equiv
      ( ( compute-proper-node-Directed-Tree (combinator-Directed-Tree T)) ∘e
        ( compute-proper-node-combinator-Directed-Tree T))
  compute-map-Σ-node-fiber-combinator-Directed-Tree (i , x) =
    inv
      ( eq-compute-proper-node-Directed-Tree
        ( combinator-Directed-Tree T)
        ( is-proper-node-inclusion-combinator-Directed-Tree T)
        ( base-index-combinator-Directed-Tree T i)
        ( walk-inclusion-combinator-Directed-Tree T i x
          ( root-Directed-Tree (T i))
          ( walk-to-root-Directed-Tree (T i) x)))

  is-equiv-map-Σ-node-fiber-combinator-Directed-Tree :
    is-equiv
      ( map-Σ
        ( λ b →
          Σ ( node-combinator-Directed-Tree T)
            ( λ x →
              walk-combinator-Directed-Tree T x
                ( node-base-Directed-Tree (combinator-Directed-Tree T) b)))
        ( base-index-combinator-Directed-Tree T)
        ( node-fiber-combinator-Directed-Tree))
  is-equiv-map-Σ-node-fiber-combinator-Directed-Tree =
    is-equiv-htpy
      ( map-equiv
        ( ( compute-proper-node-Directed-Tree (combinator-Directed-Tree T)) ∘e
          ( compute-proper-node-combinator-Directed-Tree T)))
      ( compute-map-Σ-node-fiber-combinator-Directed-Tree)
      ( is-equiv-map-equiv
        ( ( compute-proper-node-Directed-Tree (combinator-Directed-Tree T)) ∘e
          ( compute-proper-node-combinator-Directed-Tree T)))

  is-equiv-node-fiber-combinator-Directed-Tree :
    (i : I) → is-equiv (node-fiber-combinator-Directed-Tree i)
  is-equiv-node-fiber-combinator-Directed-Tree =
    is-fiberwise-equiv-is-equiv-map-Σ
      ( λ b →
        Σ ( node-combinator-Directed-Tree T)
          ( λ x →
            walk-combinator-Directed-Tree T x
              ( node-base-Directed-Tree (combinator-Directed-Tree T) b)))
      ( base-index-combinator-Directed-Tree T)
      ( node-fiber-combinator-Directed-Tree)
      ( is-equiv-base-index-combinator-Directed-Tree T)
      ( is-equiv-map-Σ-node-fiber-combinator-Directed-Tree)

  edge-fiber-combinator-Directed-Tree :
    (i : I) (x y : node-Directed-Tree (T i)) →
    edge-Directed-Tree (T i) x y →
    edge-fiber-Directed-Tree
      ( combinator-Directed-Tree T)
      ( node-base-index-combinator-Directed-Tree T i)
      ( node-fiber-combinator-Directed-Tree i x)
      ( node-fiber-combinator-Directed-Tree i y)
  pr1 (edge-fiber-combinator-Directed-Tree i x y e) =
    edge-inclusion-combinator-Directed-Tree i x y e
  pr2 (edge-fiber-combinator-Directed-Tree i x y e) =
    ap
      ( walk-inclusion-combinator-Directed-Tree T i x
        ( root-Directed-Tree (T i)))
      ( eq-is-contr (unique-walk-to-root-Directed-Tree (T i) x))

  hom-fiber-combinator-Directed-Tree :
    (i : I) →
    hom-Directed-Tree
      ( T i)
      ( fiber-Directed-Tree
        ( combinator-Directed-Tree T)
        ( node-base-index-combinator-Directed-Tree T i))
  pr1 (hom-fiber-combinator-Directed-Tree i) =
    node-fiber-combinator-Directed-Tree i
  pr2 (hom-fiber-combinator-Directed-Tree i) =
    edge-fiber-combinator-Directed-Tree i

  is-equiv-hom-fiber-combinator-Directed-Tree :
    (i : I) →
    is-equiv-hom-Directed-Tree
      ( T i)
      ( fiber-Directed-Tree
        ( combinator-Directed-Tree T)
        ( node-base-index-combinator-Directed-Tree T i))
      ( hom-fiber-combinator-Directed-Tree i)
  is-equiv-hom-fiber-combinator-Directed-Tree i =
    is-equiv-is-equiv-node-hom-Directed-Tree
      ( T i)
      ( fiber-Directed-Tree
        ( combinator-Directed-Tree T)
        ( node-base-index-combinator-Directed-Tree T i))
      ( hom-fiber-combinator-Directed-Tree i)
      ( is-equiv-node-fiber-combinator-Directed-Tree i)

  fiber-combinator-Directed-Tree :
    (i : I) →
    equiv-Directed-Tree
      ( T i)
      ( fiber-Directed-Tree
        ( combinator-Directed-Tree T)
        ( node-base-index-combinator-Directed-Tree T i))
  fiber-combinator-Directed-Tree i =
    equiv-is-equiv-hom-Directed-Tree
      ( T i)
      ( fiber-Directed-Tree
        ( combinator-Directed-Tree T)
        ( node-base-index-combinator-Directed-Tree T i))
      ( hom-fiber-combinator-Directed-Tree i)
      ( is-equiv-hom-fiber-combinator-Directed-Tree i)
```

### Any tree is the combinator tree of the fibers at the nodes equipped with edges to the root

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  node-combinator-fiber-base-Directed-Tree :
    node-combinator-Directed-Tree (fiber-base-Directed-Tree T) →
    node-Directed-Tree T
  node-combinator-fiber-base-Directed-Tree root-combinator-Directed-Tree =
    root-Directed-Tree T
  node-combinator-fiber-base-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree b (x , w)) = x

  cases-map-inv-node-combinator-fiber-base-Directed-Tree :
    (x : node-Directed-Tree T) →
    is-root-Directed-Tree T x +
    Σ ( base-Directed-Tree T)
      ( walk-Directed-Tree T x ∘ node-base-Directed-Tree T) →
    node-combinator-Directed-Tree (fiber-base-Directed-Tree T)
  cases-map-inv-node-combinator-fiber-base-Directed-Tree ._ (inl refl) =
    root-combinator-Directed-Tree
  cases-map-inv-node-combinator-fiber-base-Directed-Tree x (inr (b , w)) =
    node-inclusion-combinator-Directed-Tree b (x , w)

  map-inv-node-combinator-fiber-base-Directed-Tree :
    node-Directed-Tree T →
    node-combinator-Directed-Tree (fiber-base-Directed-Tree T)
  map-inv-node-combinator-fiber-base-Directed-Tree x =
    cases-map-inv-node-combinator-fiber-base-Directed-Tree x
      ( is-root-or-walk-to-base-Directed-Tree T x)

  cases-is-section-map-inv-node-combinator-fiber-base-Directed-Tree :
    (x : node-Directed-Tree T) →
    (H :
      is-root-Directed-Tree T x +
      Σ ( base-Directed-Tree T)
        ( walk-Directed-Tree T x ∘ node-base-Directed-Tree T)) →
    node-combinator-fiber-base-Directed-Tree
      ( cases-map-inv-node-combinator-fiber-base-Directed-Tree x H) ＝ x
  cases-is-section-map-inv-node-combinator-fiber-base-Directed-Tree ._
    ( inl refl) =
    refl
  cases-is-section-map-inv-node-combinator-fiber-base-Directed-Tree x
    ( inr (b , w)) =
    refl

  is-section-map-inv-node-combinator-fiber-base-Directed-Tree :
    ( node-combinator-fiber-base-Directed-Tree ∘
      map-inv-node-combinator-fiber-base-Directed-Tree) ~ id
  is-section-map-inv-node-combinator-fiber-base-Directed-Tree x =
    cases-is-section-map-inv-node-combinator-fiber-base-Directed-Tree x
      ( is-root-or-walk-to-base-Directed-Tree T x)

  is-retraction-map-inv-node-combinator-fiber-base-Directed-Tree :
    ( map-inv-node-combinator-fiber-base-Directed-Tree ∘
      node-combinator-fiber-base-Directed-Tree) ~ id
  is-retraction-map-inv-node-combinator-fiber-base-Directed-Tree
    root-combinator-Directed-Tree =
    ap
      ( cases-map-inv-node-combinator-fiber-base-Directed-Tree
        ( root-Directed-Tree T))
      ( eq-is-contr
        ( unique-walk-to-base-Directed-Tree T (root-Directed-Tree T)))
  is-retraction-map-inv-node-combinator-fiber-base-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree b (x , w)) =
    ap
      ( cases-map-inv-node-combinator-fiber-base-Directed-Tree x)
      ( eq-is-contr ( unique-walk-to-base-Directed-Tree T x))

  is-node-equiv-combinator-fiber-base-Directed-Tree :
    is-equiv node-combinator-fiber-base-Directed-Tree
  is-node-equiv-combinator-fiber-base-Directed-Tree =
    is-equiv-is-invertible
      map-inv-node-combinator-fiber-base-Directed-Tree
      is-section-map-inv-node-combinator-fiber-base-Directed-Tree
      is-retraction-map-inv-node-combinator-fiber-base-Directed-Tree

  node-equiv-combinator-fiber-base-Directed-Tree :
    node-combinator-Directed-Tree (fiber-base-Directed-Tree T) ≃
    node-Directed-Tree T
  pr1 node-equiv-combinator-fiber-base-Directed-Tree =
    node-combinator-fiber-base-Directed-Tree
  pr2 node-equiv-combinator-fiber-base-Directed-Tree =
    is-node-equiv-combinator-fiber-base-Directed-Tree

  edge-combinator-fiber-base-Directed-Tree :
    (x y : node-combinator-Directed-Tree (fiber-base-Directed-Tree T)) →
    edge-combinator-Directed-Tree (fiber-base-Directed-Tree T) x y →
    edge-Directed-Tree T
      ( node-combinator-fiber-base-Directed-Tree x)
      ( node-combinator-fiber-base-Directed-Tree y)
  edge-combinator-fiber-base-Directed-Tree ._ ._
    ( edge-to-root-combinator-Directed-Tree (b , e)) = e
  edge-combinator-fiber-base-Directed-Tree ._ ._
    ( edge-inclusion-combinator-Directed-Tree i (u , ._) y (e , refl)) = e

  hom-combinator-fiber-base-Directed-Tree :
    hom-Directed-Tree
      ( combinator-Directed-Tree (fiber-base-Directed-Tree T))
      ( T)
  pr1 hom-combinator-fiber-base-Directed-Tree =
    node-combinator-fiber-base-Directed-Tree
  pr2 hom-combinator-fiber-base-Directed-Tree =
    edge-combinator-fiber-base-Directed-Tree

  is-equiv-combinator-fiber-base-Directed-Tree :
    is-equiv-hom-Directed-Tree
      ( combinator-Directed-Tree (fiber-base-Directed-Tree T))
      ( T)
      ( hom-combinator-fiber-base-Directed-Tree)
  is-equiv-combinator-fiber-base-Directed-Tree =
    is-equiv-is-equiv-node-hom-Directed-Tree
      ( combinator-Directed-Tree (fiber-base-Directed-Tree T))
      ( T)
      ( hom-combinator-fiber-base-Directed-Tree)
      ( is-node-equiv-combinator-fiber-base-Directed-Tree)

  combinator-fiber-base-Directed-Tree :
    equiv-Directed-Tree
      ( combinator-Directed-Tree (fiber-base-Directed-Tree T))
      ( T)
  combinator-fiber-base-Directed-Tree =
    equiv-is-equiv-hom-Directed-Tree
      ( combinator-Directed-Tree (fiber-base-Directed-Tree T))
      ( T)
      ( hom-combinator-fiber-base-Directed-Tree)
      ( is-equiv-combinator-fiber-base-Directed-Tree)
```
