# The combinator of directed trees

```agda
{-# OPTIONS --allow-unsolved-metas #-}

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

  is-decidable-is-root-combinator-Directed-Tree :
    (x : node-combinator-Directed-Tree) →
    is-decidable (is-root-combinator-Directed-Tree x)
  is-decidable-is-root-combinator-Directed-Tree root-combinator-Directed-Tree =
    inl refl
  is-decidable-is-root-combinator-Directed-Tree
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
      ( {!!} , {!!})

  center-unique-parent-combinator-Directed-Tree' :
    ( x : node-combinator-Directed-Tree) →
    ¬ (is-root-combinator-Directed-Tree x) →
    Σ node-combinator-Directed-Tree (edge-combinator-Directed-Tree x)
  center-unique-parent-combinator-Directed-Tree'
    root-combinator-Directed-Tree f = ex-falso (f refl)
  center-unique-parent-combinator-Directed-Tree'
    ( node-inclusion-combinator-Directed-Tree a x) f = {!!}

  unique-parent-combinator-Directed-Tree' :
    ( x : node-combinator-Directed-Tree) →
    ¬ (is-root-combinator-Directed-Tree x) →
    is-contr
      ( Σ node-combinator-Directed-Tree (edge-combinator-Directed-Tree x))
  unique-parent-combinator-Directed-Tree' x f = {!!}

  unique-parent-combinator-Directed-Tree :
    unique-parent-Directed-Graph
      ( graph-combinator-Directed-Tree)
      ( root-combinator-Directed-Tree)
  unique-parent-combinator-Directed-Tree = {!!}
```
