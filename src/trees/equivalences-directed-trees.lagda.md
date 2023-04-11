# Equivalences of directed trees

```agda
module trees.equivalences-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import graph-theory.equivalences-directed-graphs
open import graph-theory.walks-directed-graphs
open import graph-theory.morphisms-directed-graphs

open import trees.directed-trees
open import trees.morphisms-directed-trees
```

</details>

## Idea

**Equivalences of directed trees** are morphisms of directed trees of which the actions on nodes and on edges are both equivalences. In other words, equivalences of directed trees are just equivalences between their underlying directed graphs.

## Definitions

### Equivalences of directed trees

```agda
equiv-Directed-Tree :
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
equiv-Directed-Tree S T =
  equiv-Directed-Graph (graph-Directed-Tree S) (graph-Directed-Tree T)

module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (e : equiv-Directed-Tree S T)
  where

  equiv-node-equiv-Directed-Tree :
    node-Directed-Tree S ≃ node-Directed-Tree T
  equiv-node-equiv-Directed-Tree =
    equiv-vertex-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  node-equiv-Directed-Tree :
    node-Directed-Tree S → node-Directed-Tree T
  node-equiv-Directed-Tree =
    vertex-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  inv-node-equiv-Directed-Tree :
    node-Directed-Tree T → node-Directed-Tree S
  inv-node-equiv-Directed-Tree =
    inv-vertex-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  issec-inv-node-equiv-Directed-Tree :
    ( node-equiv-Directed-Tree ∘ inv-node-equiv-Directed-Tree) ~ id
  issec-inv-node-equiv-Directed-Tree =
    issec-inv-vertex-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  isretr-inv-node-equiv-Directed-Tree :
    ( inv-node-equiv-Directed-Tree ∘ node-equiv-Directed-Tree) ~ id
  isretr-inv-node-equiv-Directed-Tree =
    isretr-inv-vertex-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  equiv-edge-equiv-Directed-Tree :
    (x y : node-Directed-Tree S) →
    edge-Directed-Tree S x y ≃
    edge-Directed-Tree T
      ( node-equiv-Directed-Tree x)
      ( node-equiv-Directed-Tree y)
  equiv-edge-equiv-Directed-Tree =
    equiv-edge-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  edge-equiv-Directed-Tree :
    (x y : node-Directed-Tree S) →
    edge-Directed-Tree S x y →
    edge-Directed-Tree T
      ( node-equiv-Directed-Tree x)
      ( node-equiv-Directed-Tree y)
  edge-equiv-Directed-Tree =
    edge-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  hom-equiv-Directed-Tree : hom-Directed-Tree S T
  hom-equiv-Directed-Tree =
    hom-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  equiv-children-equiv-Directed-Tree :
    (x : node-Directed-Tree S) →
    ( Σ (node-Directed-Tree S) (λ y → edge-Directed-Tree S y x)) ≃
    ( Σ ( node-Directed-Tree T)
        ( λ y → edge-Directed-Tree T y (node-equiv-Directed-Tree x)))
  equiv-children-equiv-Directed-Tree x =
    equiv-Σ
      ( λ y → edge-Directed-Tree T y (node-equiv-Directed-Tree x))
      ( equiv-node-equiv-Directed-Tree)
      ( λ y → equiv-edge-equiv-Directed-Tree y x)
```

### Identity equivalences of directed trees

```agda
id-equiv-Directed-Tree :
  {l1 l2 : Level} (T : Directed-Tree l1 l2) → equiv-Directed-Tree T T
pr1 (id-equiv-Directed-Tree T) = id-equiv
pr2 (id-equiv-Directed-Tree T) x y = id-equiv
```

### Homotopies of equivalences of directed trees

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (f g : equiv-Directed-Tree S T)
  where
  
  htpy-equiv-Directed-Tree : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-equiv-Directed-Tree =
    htpy-hom-Directed-Tree S T
      ( hom-equiv-Directed-Tree S T f)
      ( hom-equiv-Directed-Tree S T g)

  node-htpy-equiv-Directed-Tree :
    htpy-equiv-Directed-Tree →
    node-equiv-Directed-Tree S T f ~ node-equiv-Directed-Tree S T g
  node-htpy-equiv-Directed-Tree =
    node-htpy-hom-Directed-Tree S T
      ( hom-equiv-Directed-Tree S T f)
      ( hom-equiv-Directed-Tree S T g)

  edge-htpy-equiv-Directed-Tree :
    (α : htpy-equiv-Directed-Tree) (x y : node-Directed-Tree S)
    (e : edge-Directed-Tree S x y) →
    binary-tr
      ( edge-Directed-Tree T)
      ( node-htpy-equiv-Directed-Tree α x)
      ( node-htpy-equiv-Directed-Tree α y)
      ( edge-equiv-Directed-Tree S T f x y e) ＝
    edge-equiv-Directed-Tree S T g x y e
  edge-htpy-equiv-Directed-Tree =
    edge-htpy-hom-Directed-Tree S T
      ( hom-equiv-Directed-Tree S T f)
      ( hom-equiv-Directed-Tree S T g)
```

### The reflexivity homotopy of equivalences of directed trees

```agda
refl-htpy-equiv-Directed-Tree :
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (f : equiv-Directed-Tree S T) → htpy-equiv-Directed-Tree S T f f
refl-htpy-equiv-Directed-Tree S T f =
  refl-htpy-hom-Directed-Tree S T (hom-equiv-Directed-Tree S T f)
```

## Properties

### Homotopies characterize the identity type of equivalences of directed trees

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (e : equiv-Directed-Tree S T)
  where

  is-contr-total-htpy-equiv-Directed-Tree :
    is-contr (Σ (equiv-Directed-Tree S T) (htpy-equiv-Directed-Tree S T e))
  is-contr-total-htpy-equiv-Directed-Tree =
    is-contr-total-htpy-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  htpy-eq-equiv-Directed-Tree :
    (f : equiv-Directed-Tree S T) → (e ＝ f) → htpy-equiv-Directed-Tree S T e f
  htpy-eq-equiv-Directed-Tree =
    htpy-eq-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  is-equiv-htpy-eq-equiv-Directed-Tree :
    (f : equiv-Directed-Tree S T) → is-equiv (htpy-eq-equiv-Directed-Tree f)
  is-equiv-htpy-eq-equiv-Directed-Tree =
    is-equiv-htpy-eq-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  extensionality-equiv-Directed-Tree :
    (f : equiv-Directed-Tree S T) → (e ＝ f) ≃ htpy-equiv-Directed-Tree S T e f
  extensionality-equiv-Directed-Tree =
    extensionality-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  eq-htpy-equiv-Directed-Tree :
    (f : equiv-Directed-Tree S T) → htpy-equiv-Directed-Tree S T e f → e ＝ f
  eq-htpy-equiv-Directed-Tree =
    eq-htpy-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)
```

### Equivalences of directed trees preserve the root

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (e : equiv-Directed-Tree S T)
  where

  preserves-root-equiv-Directed-Tree :
    node-equiv-Directed-Tree S T e (root-Directed-Tree S) ＝
    root-Directed-Tree T
  preserves-root-equiv-Directed-Tree =
    inv
      ( uniqueness-root-Directed-Tree T
        ( pair
          ( node-equiv-Directed-Tree S T e (root-Directed-Tree S))
          ( λ y →
            is-contr-equiv'
              ( walk-Directed-Tree S
                ( inv-node-equiv-Directed-Tree S T e y)
                ( root-Directed-Tree S))
              ( ( equiv-binary-tr
                  ( walk-Directed-Graph (graph-Directed-Tree T))
                  ( issec-inv-node-equiv-Directed-Tree S T e y)
                  ( refl)) ∘e
                ( equiv-walk-equiv-Directed-Graph
                  ( graph-Directed-Tree S)
                  ( graph-Directed-Tree T)
                  ( e)))
              ( is-tree-Directed-Tree' S
                ( inv-node-equiv-Directed-Tree S T e y)))))
```
