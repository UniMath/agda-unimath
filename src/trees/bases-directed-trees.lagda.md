# Bases of directed trees

```agda
module trees.bases-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.universe-levels

open import graph-theory.walks-directed-graphs

open import trees.directed-trees
```

</details>

## Idea

The base of a directed tree consists of the nodes equipped with an edge to the root.

## Definition

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where
  
  base-Directed-Tree : UU (l1 ⊔ l2)
  base-Directed-Tree = children-Directed-Tree T (root-Directed-Tree T)

  module _
    (b : base-Directed-Tree)
    where

    node-base-Directed-Tree : node-Directed-Tree T
    node-base-Directed-Tree = pr1 b

    edge-base-Directed-Tree :
      edge-Directed-Tree T node-base-Directed-Tree (root-Directed-Tree T)
    edge-base-Directed-Tree = pr2 b
```

## Properties

### The root is not a base element

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  is-not-root-node-base-Directed-Tree :
    (b : base-Directed-Tree T) →
    ¬ (is-root-Directed-Tree T (node-base-Directed-Tree T b))
  is-not-root-node-base-Directed-Tree (x , e) refl =
    no-parent-root-Directed-Tree T (x , e)

  no-walk-to-base-root-Directed-Tree :
    (b : base-Directed-Tree T) →
    ¬ ( walk-Directed-Tree T
        ( root-Directed-Tree T)
        ( node-base-Directed-Tree T b))
  no-walk-to-base-root-Directed-Tree
    ( pair .(root-Directed-Tree T) e)
    refl-walk-Directed-Graph =
    no-parent-root-Directed-Tree T (root-Directed-Tree T , e)
  no-walk-to-base-root-Directed-Tree b (cons-walk-Directed-Graph e w) =
    no-parent-root-Directed-Tree T (_ , e)
```

### There are no edges between base elements

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  no-edge-base-Directed-Tree :
    (a b : base-Directed-Tree T) →
    ¬ ( edge-Directed-Tree T
        ( node-base-Directed-Tree T a)
        ( node-base-Directed-Tree T b))
  no-edge-base-Directed-Tree a b e =
    ex-falso
      ( is-not-one-two-ℕ
        ( ap
          ( length-walk-Directed-Graph (graph-Directed-Tree T))
          ( eq-is-contr'
            ( is-tree-Directed-Tree' T (node-base-Directed-Tree T a))
            ( cons-walk-Directed-Tree T e
              ( unit-walk-Directed-Tree T (edge-base-Directed-Tree T b)))
            ( unit-walk-Directed-Tree T (edge-base-Directed-Tree T a)))))
```

### For any node `x`, the coproduct of `is-root x` and the type of base elements `b` equipped with a walk from `x` to `b` is contractible

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  cons-cases-center-walk-to-base-Directed-Tree :
    {x y : node-Directed-Tree T} (e : edge-Directed-Tree T x y) →
    (w : walk-Directed-Tree T y (root-Directed-Tree T)) →
    Σ (base-Directed-Tree T) (walk-Directed-Tree T x ∘ pr1)
  cons-cases-center-walk-to-base-Directed-Tree e refl-walk-Directed-Graph =
    (_ , e) , refl-walk-Directed-Tree T
  cons-cases-center-walk-to-base-Directed-Tree e
    ( cons-walk-Directed-Graph f w) =
    tot
      ( λ u → cons-walk-Directed-Tree T e)
      ( cons-cases-center-walk-to-base-Directed-Tree f w)

  cases-center-walk-to-base-Directed-Tree :
    {x : node-Directed-Tree T}
    (w : walk-Directed-Tree T x (root-Directed-Tree T)) →
    is-root-Directed-Tree T x +
    Σ (base-Directed-Tree T) (walk-Directed-Tree T x ∘ pr1)
  cases-center-walk-to-base-Directed-Tree refl-walk-Directed-Graph = inl refl
  cases-center-walk-to-base-Directed-Tree (cons-walk-Directed-Graph e w) =
    inr (cons-cases-center-walk-to-base-Directed-Tree e w)

  center-walk-to-base-Directed-Tree :
    (x : node-Directed-Tree T) → 
    is-root-Directed-Tree T x +
    Σ (base-Directed-Tree T) (walk-Directed-Tree T x ∘ pr1)
  center-walk-to-base-Directed-Tree x =
    cases-center-walk-to-base-Directed-Tree (walk-to-root-Directed-Tree T x)

  cons-cases-contraction-walk-to-base-Directed-Tree :
    {x y : node-Directed-Tree T} (e : edge-Directed-Tree T x y) →
    (w : walk-Directed-Tree T y (root-Directed-Tree T))
    (u : Σ (base-Directed-Tree T) (walk-Directed-Tree T x ∘ pr1)) →
    cons-cases-center-walk-to-base-Directed-Tree e w ＝ u
  cons-cases-contraction-walk-to-base-Directed-Tree e
    ( refl-walk-Directed-Graph)
    ( (z , f) , refl-walk-Directed-Graph) =
    ap
      ( λ i → ((z , i) , refl-walk-Directed-Graph))
      ( eq-is-contr
        ( is-proof-irrelevant-edge-to-root-Directed-Tree T z e))
  cons-cases-contraction-walk-to-base-Directed-Tree {x} e
    ( refl-walk-Directed-Graph)
    ( (z , f) , cons-walk-Directed-Graph {_} {y} g v) =
    ex-falso
      ( no-walk-to-base-root-Directed-Tree T
        ( z , f)
        ( tr
          ( λ u → walk-Directed-Tree T u z)
          ( ap pr1
            ( eq-parent-Directed-Tree T (y , g) (root-Directed-Tree T , e)))
          ( v)))
  cons-cases-contraction-walk-to-base-Directed-Tree e
    ( cons-walk-Directed-Graph {y} {z} g w)
    ( (u , f) , refl-walk-Directed-Graph) =
    ex-falso
      ( no-parent-root-Directed-Tree T
        ( tr
          ( λ i → Σ (node-Directed-Tree T) (edge-Directed-Tree T i))
          ( ap pr1
            ( eq-parent-Directed-Tree T (y , e) (root-Directed-Tree T , f)))
          ( z , g)))
  cons-cases-contraction-walk-to-base-Directed-Tree {x} {y} e
    ( cons-walk-Directed-Graph {y} {z} g w)
    ( (u , f) , cons-walk-Directed-Graph {_} {y'} e' v) =
    ( ap
      ( tot (λ u → cons-walk-Directed-Tree T e))
      ( cons-cases-contraction-walk-to-base-Directed-Tree g w
        ( (u , f) , tr-walk-eq-parent-Directed-Tree T (y' , e') (y , e) v))) ∙
    ( ap
      ( pair (u , f))
      ( eq-tr-walk-eq-parent-Directed-Tree T (y' , e') (y , e) v))
    where
    p : (y , e) ＝ (y' , e')
    p = eq-parent-Directed-Tree T (y , e) (y' , e')

  cases-contraction-walk-to-base-Directed-Tree :
    {x : node-Directed-Tree T}
    (w : walk-Directed-Tree T x (root-Directed-Tree T)) →
    (u : 
      is-root-Directed-Tree T x +
      Σ (base-Directed-Tree T) (walk-Directed-Tree T x ∘ pr1)) →
    cases-center-walk-to-base-Directed-Tree w ＝ u
  cases-contraction-walk-to-base-Directed-Tree
    ( refl-walk-Directed-Graph)
    ( inl p) =
    ap inl (eq-is-contr (is-contr-loop-space-root-Directed-Tree T))
  cases-contraction-walk-to-base-Directed-Tree refl-walk-Directed-Graph
    ( inr (b , w)) =
    ex-falso (no-walk-to-base-root-Directed-Tree T b w)
  cases-contraction-walk-to-base-Directed-Tree
    ( cons-walk-Directed-Graph e w)
    ( inl refl) =
    ex-falso (no-parent-root-Directed-Tree T (_ , e))
  cases-contraction-walk-to-base-Directed-Tree
    ( cons-walk-Directed-Graph e w) (inr u) =
    ap inr (cons-cases-contraction-walk-to-base-Directed-Tree e w u)
  
  contraction-walk-to-base-Directed-Tree :
    (x : node-Directed-Tree T)
    ( w :
      is-root-Directed-Tree T x +
      Σ (base-Directed-Tree T) (walk-Directed-Tree T x ∘ pr1)) →
    center-walk-to-base-Directed-Tree x ＝ w
  contraction-walk-to-base-Directed-Tree x =
    cases-contraction-walk-to-base-Directed-Tree
      ( walk-to-root-Directed-Tree T x)
```
