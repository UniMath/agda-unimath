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
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.isolated-points
open import foundation.negation
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.morphisms-directed-graphs
open import graph-theory.walks-directed-graphs

open import trees.directed-trees
```

</details>

## Idea

Any family of directed trees can be combined into a single directed tree with a
new root.

## Definitions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (T : A → Directed-Tree l2 l3)
  where

  data node-combinator-Directed-Tree : UU (l1 ⊔ l2) where
    root-combinator-Directed-Tree : node-combinator-Directed-Tree
    node-inclusion-combinator-Directed-Tree :
      (a : A) → node-Directed-Tree (T a) → node-combinator-Directed-Tree

  data
    edge-combinator-Directed-Tree :
      ( x y : node-combinator-Directed-Tree) → UU (l1 ⊔ l2 ⊔ l3) where
    edge-to-root-combinator-Directed-Tree :
      (a : A) →
      edge-combinator-Directed-Tree
        ( node-inclusion-combinator-Directed-Tree a (root-Directed-Tree (T a)))
        ( root-combinator-Directed-Tree)
    edge-inclusion-combinator-Directed-Tree :
      (a : A) (x y : node-Directed-Tree (T a)) →
      edge-Directed-Tree (T a) x y →
      edge-combinator-Directed-Tree
        ( node-inclusion-combinator-Directed-Tree a x)
        ( node-inclusion-combinator-Directed-Tree a y)

  graph-combinator-Directed-Tree : Directed-Graph (l1 ⊔ l2) (l1 ⊔ l2 ⊔ l3)
  pr1 graph-combinator-Directed-Tree = node-combinator-Directed-Tree
  pr2 graph-combinator-Directed-Tree = edge-combinator-Directed-Tree

  inclusion-combinator-Directed-Tree :
    (a : A) →
    hom-Directed-Graph
      ( graph-Directed-Tree (T a))
      ( graph-combinator-Directed-Tree)
  pr1 (inclusion-combinator-Directed-Tree a) =
    node-inclusion-combinator-Directed-Tree a
  pr2 (inclusion-combinator-Directed-Tree a) =
    edge-inclusion-combinator-Directed-Tree a

  walk-combinator-Directed-Tree :
    ( x y : node-combinator-Directed-Tree) → UU (l1 ⊔ l2 ⊔ l3)
  walk-combinator-Directed-Tree =
    walk-Directed-Graph graph-combinator-Directed-Tree

  walk-inclusion-combinator-Directed-Tree :
    (a : A) (x y : node-Directed-Tree (T a)) →
    walk-Directed-Graph (graph-Directed-Tree (T a)) x y →
    walk-combinator-Directed-Tree
      ( node-inclusion-combinator-Directed-Tree a x)
      ( node-inclusion-combinator-Directed-Tree a y)
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
    ( node-inclusion-combinator-Directed-Tree a x) =
    snoc-walk-Directed-Graph
      ( graph-combinator-Directed-Tree)
      ( walk-inclusion-combinator-Directed-Tree a x
        ( root-Directed-Tree (T a))
        ( walk-to-root-Directed-Tree (T a) x))
      ( edge-to-root-combinator-Directed-Tree a)

  is-root-combinator-Directed-Tree :
    node-combinator-Directed-Tree → UU (l1 ⊔ l2)
  is-root-combinator-Directed-Tree x = root-combinator-Directed-Tree ＝ x

  is-isolated-root-combinator-Directed-Tree :
    is-isolated root-combinator-Directed-Tree
  is-isolated-root-combinator-Directed-Tree root-combinator-Directed-Tree =
    inl refl
  is-isolated-root-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree a x) =
    inr (λ ())

  cases-center-unique-parent-combinator-Directed-Tree' :
    (a : A) (x : node-Directed-Tree (T a)) →
    is-decidable (is-root-Directed-Tree (T a) x) →
    Σ ( node-combinator-Directed-Tree)
      ( edge-combinator-Directed-Tree
        ( node-inclusion-combinator-Directed-Tree a x))
  cases-center-unique-parent-combinator-Directed-Tree' a ._ (inl refl) =
    ( root-combinator-Directed-Tree , edge-to-root-combinator-Directed-Tree a)
  cases-center-unique-parent-combinator-Directed-Tree' a x (inr f) =
    map-Σ
      ( edge-combinator-Directed-Tree
        ( node-inclusion-combinator-Directed-Tree a x))
      ( node-inclusion-combinator-Directed-Tree a)
      ( edge-inclusion-combinator-Directed-Tree a x)
      ( parent-is-not-root-Directed-Tree (T a) x f)

  center-unique-parent-combinator-Directed-Tree' :
    ( x : node-combinator-Directed-Tree) →
    ¬ (is-root-combinator-Directed-Tree x) →
    Σ node-combinator-Directed-Tree (edge-combinator-Directed-Tree x)
  center-unique-parent-combinator-Directed-Tree'
    root-combinator-Directed-Tree f = ex-falso (f refl)
  center-unique-parent-combinator-Directed-Tree'
    ( node-inclusion-combinator-Directed-Tree a x) f =
    cases-center-unique-parent-combinator-Directed-Tree' a x
      ( is-isolated-root-Directed-Tree (T a) x)

  cases-center-unique-parent-combinator-Directed-Tree :
    (a : A) (x : node-Directed-Tree (T a)) →
    is-decidable (is-root-Directed-Tree (T a) x) →
    Σ ( node-combinator-Directed-Tree)
      ( edge-combinator-Directed-Tree
        ( node-inclusion-combinator-Directed-Tree a x))
  cases-center-unique-parent-combinator-Directed-Tree a ._ (inl refl) =
    root-combinator-Directed-Tree ,
    edge-to-root-combinator-Directed-Tree a
  cases-center-unique-parent-combinator-Directed-Tree a x (inr f) =
    map-Σ
      ( edge-combinator-Directed-Tree
        ( node-inclusion-combinator-Directed-Tree a x))
      ( node-inclusion-combinator-Directed-Tree a)
      ( edge-inclusion-combinator-Directed-Tree a x)
      ( parent-is-not-root-Directed-Tree (T a) x f)

  center-unique-parent-combinator-Directed-Tree :
    (x : node-combinator-Directed-Tree) →
    is-root-combinator-Directed-Tree x +
    Σ node-combinator-Directed-Tree (edge-combinator-Directed-Tree x)
  center-unique-parent-combinator-Directed-Tree root-combinator-Directed-Tree =
    inl refl
  center-unique-parent-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree a x) =
    inr
      ( cases-center-unique-parent-combinator-Directed-Tree a x
        ( is-isolated-root-Directed-Tree (T a) x))

  cases-contraction-unique-parent-combinator-Directed-Tree :
    (a : A) (x : node-Directed-Tree (T a)) →
    (d : is-decidable (is-root-Directed-Tree (T a) x)) →
    ( p :
      Σ ( node-combinator-Directed-Tree)
        ( edge-combinator-Directed-Tree
          ( node-inclusion-combinator-Directed-Tree a x))) →
    cases-center-unique-parent-combinator-Directed-Tree a x d ＝ p
  cases-contraction-unique-parent-combinator-Directed-Tree a ._
    ( inl r)
    ( ._ , edge-to-root-combinator-Directed-Tree .a) =
    ap
      ( λ u →
        cases-center-unique-parent-combinator-Directed-Tree a
          ( root-Directed-Tree (T a))
          ( inl u))
      ( eq-refl-root-Directed-Tree (T a) r)
  cases-contraction-unique-parent-combinator-Directed-Tree a ._
    ( inr f)
    ( ._ , edge-to-root-combinator-Directed-Tree .a) =
    ex-falso (f refl)
  cases-contraction-unique-parent-combinator-Directed-Tree a ._
    ( inl refl)
    ( ._ , edge-inclusion-combinator-Directed-Tree .a ._ y e) =
    ex-falso (no-parent-root-Directed-Tree (T a) (y , e))
  cases-contraction-unique-parent-combinator-Directed-Tree a x
    ( inr f)
    ( ._ , edge-inclusion-combinator-Directed-Tree .a .x y e) =
    ap
      ( map-Σ
        ( edge-combinator-Directed-Tree
          ( node-inclusion-combinator-Directed-Tree a x))
        ( node-inclusion-combinator-Directed-Tree a)
        ( edge-inclusion-combinator-Directed-Tree a x))
      ( eq-is-contr (unique-parent-is-not-root-Directed-Tree (T a) x f))

  contraction-unique-parent-combinator-Directed-Tree :
    (x : node-combinator-Directed-Tree) →
    (p : is-root-combinator-Directed-Tree x +
         Σ node-combinator-Directed-Tree (edge-combinator-Directed-Tree x)) →
    center-unique-parent-combinator-Directed-Tree x ＝ p
  contraction-unique-parent-combinator-Directed-Tree ._ (inl refl) = refl
  contraction-unique-parent-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree a x)
    ( inr (y , e)) =
    ap
      ( inr)
      ( cases-contraction-unique-parent-combinator-Directed-Tree a x
        ( is-isolated-root-Directed-Tree (T a) x)
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
