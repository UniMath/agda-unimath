# The combinator of directed trees

```agda
module trees.combinator-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.isolated-points
open import foundation.negation
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.morphisms-directed-graphs
open import graph-theory.walks-directed-graphs

open import trees.directed-trees
open import trees.fibers-directed-trees
```

</details>

## Idea

Any family of directed trees can be combined into a single directed tree with a
new root.

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

  cases-center-unique-parent-combinator-Directed-Tree' :
    (i : I) (x : node-Directed-Tree (T i)) →
    is-decidable (is-root-Directed-Tree (T i) x) →
    Σ ( node-combinator-Directed-Tree)
      ( edge-combinator-Directed-Tree
        ( node-inclusion-combinator-Directed-Tree i x))
  cases-center-unique-parent-combinator-Directed-Tree' a ._ (inl refl) =
    ( root-combinator-Directed-Tree , edge-to-root-combinator-Directed-Tree a)
  cases-center-unique-parent-combinator-Directed-Tree' i x (inr f) =
    map-Σ
      ( edge-combinator-Directed-Tree
        ( node-inclusion-combinator-Directed-Tree i x))
      ( node-inclusion-combinator-Directed-Tree i)
      ( edge-inclusion-combinator-Directed-Tree i x)
      ( parent-is-not-root-Directed-Tree (T i) x f)

  center-unique-parent-combinator-Directed-Tree' :
    ( x : node-combinator-Directed-Tree) →
    ¬ (is-root-combinator-Directed-Tree x) →
    Σ node-combinator-Directed-Tree (edge-combinator-Directed-Tree x)
  center-unique-parent-combinator-Directed-Tree'
    root-combinator-Directed-Tree f = ex-falso (f refl)
  center-unique-parent-combinator-Directed-Tree'
    ( node-inclusion-combinator-Directed-Tree i x) f =
    cases-center-unique-parent-combinator-Directed-Tree' i x
      ( is-isolated-root-Directed-Tree (T i) x)

  cases-center-unique-parent-combinator-Directed-Tree :
    (i : I) (x : node-Directed-Tree (T i)) →
    is-decidable (is-root-Directed-Tree (T i) x) →
    Σ ( node-combinator-Directed-Tree)
      ( edge-combinator-Directed-Tree
        ( node-inclusion-combinator-Directed-Tree i x))
  cases-center-unique-parent-combinator-Directed-Tree i ._ (inl refl) =
    root-combinator-Directed-Tree ,
    edge-to-root-combinator-Directed-Tree i
  cases-center-unique-parent-combinator-Directed-Tree i x (inr f) =
    map-Σ
      ( edge-combinator-Directed-Tree
        ( node-inclusion-combinator-Directed-Tree i x))
      ( node-inclusion-combinator-Directed-Tree i)
      ( edge-inclusion-combinator-Directed-Tree i x)
      ( parent-is-not-root-Directed-Tree (T i) x f)

  center-unique-parent-combinator-Directed-Tree :
    (x : node-combinator-Directed-Tree) →
    is-root-combinator-Directed-Tree x +
    Σ node-combinator-Directed-Tree (edge-combinator-Directed-Tree x)
  center-unique-parent-combinator-Directed-Tree root-combinator-Directed-Tree =
    inl refl
  center-unique-parent-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x) =
    inr
      ( cases-center-unique-parent-combinator-Directed-Tree i x
        ( is-isolated-root-Directed-Tree (T i) x))

  cases-contraction-unique-parent-combinator-Directed-Tree :
    (i : I) (x : node-Directed-Tree (T i)) →
    (d : is-decidable (is-root-Directed-Tree (T i) x)) →
    ( p :
      Σ ( node-combinator-Directed-Tree)
        ( edge-combinator-Directed-Tree
          ( node-inclusion-combinator-Directed-Tree i x))) →
    cases-center-unique-parent-combinator-Directed-Tree i x d ＝ p
  cases-contraction-unique-parent-combinator-Directed-Tree i ._
    ( inl r)
    ( ._ , edge-to-root-combinator-Directed-Tree .i) =
    ap
      ( λ u →
        cases-center-unique-parent-combinator-Directed-Tree i
          ( root-Directed-Tree (T i))
          ( inl u))
      ( eq-refl-root-Directed-Tree (T i) r)
  cases-contraction-unique-parent-combinator-Directed-Tree i ._
    ( inr f)
    ( ._ , edge-to-root-combinator-Directed-Tree .i) =
    ex-falso (f refl)
  cases-contraction-unique-parent-combinator-Directed-Tree i ._
    ( inl refl)
    ( ._ , edge-inclusion-combinator-Directed-Tree .i ._ y e) =
    ex-falso (no-parent-root-Directed-Tree (T i) (y , e))
  cases-contraction-unique-parent-combinator-Directed-Tree i x
    ( inr f)
    ( ._ , edge-inclusion-combinator-Directed-Tree .i .x y e) =
    ap
      ( map-Σ
        ( edge-combinator-Directed-Tree
          ( node-inclusion-combinator-Directed-Tree i x))
        ( node-inclusion-combinator-Directed-Tree i)
        ( edge-inclusion-combinator-Directed-Tree i x))
      ( eq-is-contr (unique-parent-is-not-root-Directed-Tree (T i) x f))

  contraction-unique-parent-combinator-Directed-Tree :
    (x : node-combinator-Directed-Tree) →
    (p : is-root-combinator-Directed-Tree x +
         Σ node-combinator-Directed-Tree (edge-combinator-Directed-Tree x)) →
    center-unique-parent-combinator-Directed-Tree x ＝ p
  contraction-unique-parent-combinator-Directed-Tree ._ (inl refl) = refl
  contraction-unique-parent-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x)
    ( inr (y , e)) =
    ap
      ( inr)
      ( cases-contraction-unique-parent-combinator-Directed-Tree i x
        ( is-isolated-root-Directed-Tree (T i) x)
        ( y , e))

  unique-parent-combinator-Directed-Tree :
    unique-parent-Directed-Graph
      ( graph-combinator-Directed-Tree)
      ( root-combinator-Directed-Tree)
  pr1 (unique-parent-combinator-Directed-Tree x) =
    center-unique-parent-combinator-Directed-Tree x
  pr2 (unique-parent-combinator-Directed-Tree x) =
    contraction-unique-parent-combinator-Directed-Tree x

  is-tree-combinator-Directed-Tree :
    is-tree-Directed-Graph graph-combinator-Directed-Tree
  is-tree-combinator-Directed-Tree =
    is-tree-unique-parent-Directed-Graph
      graph-combinator-Directed-Tree
      root-combinator-Directed-Tree
      unique-parent-combinator-Directed-Tree
      walk-to-root-combinator-Directed-Tree

  combinator-Directed-Tree : Directed-Tree (l1 ⊔ l2) (l1 ⊔ l2 ⊔ l3)
  pr1 combinator-Directed-Tree = graph-combinator-Directed-Tree
  pr2 combinator-Directed-Tree = is-tree-combinator-Directed-Tree
```

## Properties

### The type of children of `x : T i` is equivalent to the type of children of the inclusion of `x` in `combinator T`

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (T : I → Directed-Tree l2 l3)
  (i : I) (x : node-Directed-Tree (T i))
  where

  map-children-combinator-Directed-Tree :
    Σ ( node-Directed-Tree (T i)) (λ y → edge-Directed-Tree (T i) y x) →
    Σ ( node-combinator-Directed-Tree T)
      ( λ y →
        edge-combinator-Directed-Tree T y
          ( node-inclusion-combinator-Directed-Tree i x))
  pr1 (map-children-combinator-Directed-Tree (y , e)) =
    node-inclusion-combinator-Directed-Tree i y
  pr2 (map-children-combinator-Directed-Tree (y , e)) =
    edge-inclusion-combinator-Directed-Tree i y x e

  map-inv-children-combinator-Directed-Tree :
    Σ ( node-combinator-Directed-Tree T)
      ( λ y →
        edge-combinator-Directed-Tree T y
          ( node-inclusion-combinator-Directed-Tree i x)) →
    Σ ( node-Directed-Tree (T i)) (λ y → edge-Directed-Tree (T i) y x)
  map-inv-children-combinator-Directed-Tree
    ( ._ , edge-inclusion-combinator-Directed-Tree .i y .x e) =
    ( y , e)

  issec-map-inv-children-combinator-Directed-Tree :
    ( map-children-combinator-Directed-Tree ∘
      map-inv-children-combinator-Directed-Tree) ~ id
  issec-map-inv-children-combinator-Directed-Tree
    ( ._ , edge-inclusion-combinator-Directed-Tree .i y .x e) =
    refl

  isretr-map-inv-children-combinator-Directed-Tree :
    ( map-inv-children-combinator-Directed-Tree ∘
      map-children-combinator-Directed-Tree) ~ id
  isretr-map-inv-children-combinator-Directed-Tree (y , e) = refl

  is-equiv-map-children-combinator-Directed-Tree :
    is-equiv map-children-combinator-Directed-Tree
  is-equiv-map-children-combinator-Directed-Tree =
    is-equiv-has-inverse
      map-inv-children-combinator-Directed-Tree
      issec-map-inv-children-combinator-Directed-Tree
      isretr-map-inv-children-combinator-Directed-Tree

  children-combinator-Directed-Tree :
    Σ ( node-Directed-Tree (T i)) (λ y → edge-Directed-Tree (T i) y x) ≃
    Σ ( node-combinator-Directed-Tree T)
      ( λ y →
        edge-combinator-Directed-Tree T y
          ( node-inclusion-combinator-Directed-Tree i x))
  pr1 children-combinator-Directed-Tree =
    map-children-combinator-Directed-Tree
  pr2 children-combinator-Directed-Tree =
    is-equiv-map-children-combinator-Directed-Tree
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

### Any tree is the combinator tree of the fibers at the nodes equipped with edges to the root

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  private
    fib-T : (i : base-Directed-Tree T) → Directed-Tree (l1 ⊔ l2) (l1 ⊔ l2)
    fib-T (x , e) = fiber-Directed-Tree T x
```
