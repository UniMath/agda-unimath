# Functoriality of the fiber operation on directed trees

```agda
module trees.functoriality-fiber-directed-tree where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import graph-theory.walks-directed-graphs

open import trees.directed-trees
open import trees.equivalences-directed-trees
open import trees.fibers-directed-trees
open import trees.morphisms-directed-trees
```

</details>

## Idea

Any [morphism](trees.morphisms-directed-trees.md) `f : S → T` of
[directed trees](trees.directed-trees.md) induces for any node `x ∈ S` a
morphism of [fibers](trees.fibers-directed-trees.md) of directed trees.

## Definitions

### The action on fibers of morphisms of directed trees

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (f : hom-Directed-Tree S T) (x : node-Directed-Tree S)
  where

  node-fiber-hom-Directed-Tree :
    node-fiber-Directed-Tree S x →
    node-fiber-Directed-Tree T (node-hom-Directed-Tree S T f x)
  node-fiber-hom-Directed-Tree =
    map-Σ
      ( λ y → walk-Directed-Tree T y (node-hom-Directed-Tree S T f x))
      ( node-hom-Directed-Tree S T f)
      ( λ y → walk-hom-Directed-Tree S T f {y} {x})

  edge-fiber-hom-Directed-Tree :
    (y z : node-fiber-Directed-Tree S x) →
    edge-fiber-Directed-Tree S x y z →
    edge-fiber-Directed-Tree T
      ( node-hom-Directed-Tree S T f x)
      ( node-fiber-hom-Directed-Tree y)
      ( node-fiber-hom-Directed-Tree z)
  edge-fiber-hom-Directed-Tree (y , v) (z , w) =
    map-Σ
      ( λ e →
        walk-hom-Directed-Tree S T f v ＝
        cons-walk-Directed-Graph e (walk-hom-Directed-Tree S T f w))
      ( edge-hom-Directed-Tree S T f)
      ( λ e → ap (walk-hom-Directed-Tree S T f))

  fiber-hom-Directed-Tree :
    hom-Directed-Tree
      ( fiber-Directed-Tree S x)
      ( fiber-Directed-Tree T (node-hom-Directed-Tree S T f x))
  pr1 fiber-hom-Directed-Tree = node-fiber-hom-Directed-Tree
  pr2 fiber-hom-Directed-Tree = edge-fiber-hom-Directed-Tree
```

### The action on fibers of equivalences of directed trees

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (f : equiv-Directed-Tree S T) (x : node-Directed-Tree S)
  where

  equiv-node-fiber-equiv-Directed-Tree :
    node-fiber-Directed-Tree S x ≃
    node-fiber-Directed-Tree T (node-equiv-Directed-Tree S T f x)
  equiv-node-fiber-equiv-Directed-Tree =
    equiv-Σ
      ( λ y → walk-Directed-Tree T y (node-equiv-Directed-Tree S T f x))
      ( node-equiv-equiv-Directed-Tree S T f)
      ( λ y → equiv-walk-equiv-Directed-Tree S T f {y} {x})

  node-fiber-equiv-Directed-Tree :
    node-fiber-Directed-Tree S x →
    node-fiber-Directed-Tree T (node-equiv-Directed-Tree S T f x)
  node-fiber-equiv-Directed-Tree =
    map-equiv equiv-node-fiber-equiv-Directed-Tree

  edge-equiv-fiber-equiv-Directed-Tree :
    (y z : node-fiber-Directed-Tree S x) →
    edge-fiber-Directed-Tree S x y z ≃
    edge-fiber-Directed-Tree T
      ( node-equiv-Directed-Tree S T f x)
      ( node-fiber-equiv-Directed-Tree y)
      ( node-fiber-equiv-Directed-Tree z)
  edge-equiv-fiber-equiv-Directed-Tree (y , v) (z , w) =
    equiv-Σ
      ( λ e →
        walk-equiv-Directed-Tree S T f v ＝
        cons-walk-Directed-Graph e (walk-equiv-Directed-Tree S T f w))
      ( edge-equiv-equiv-Directed-Tree S T f y z)
      ( λ e →
        equiv-ap
          ( equiv-walk-equiv-Directed-Tree S T f)
          ( v)
          ( cons-walk-Directed-Graph e w))

  edge-fiber-equiv-Directed-Tree :
    (y z : node-fiber-Directed-Tree S x) →
    edge-fiber-Directed-Tree S x y z →
    edge-fiber-Directed-Tree T
      ( node-equiv-Directed-Tree S T f x)
      ( node-fiber-equiv-Directed-Tree y)
      ( node-fiber-equiv-Directed-Tree z)
  edge-fiber-equiv-Directed-Tree y z =
    map-equiv (edge-equiv-fiber-equiv-Directed-Tree y z)

  fiber-equiv-Directed-Tree :
    equiv-Directed-Tree
      ( fiber-Directed-Tree S x)
      ( fiber-Directed-Tree T (node-equiv-Directed-Tree S T f x))
  pr1 fiber-equiv-Directed-Tree =
    equiv-node-fiber-equiv-Directed-Tree
  pr2 fiber-equiv-Directed-Tree =
    edge-equiv-fiber-equiv-Directed-Tree
```
