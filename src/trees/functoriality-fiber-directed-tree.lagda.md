# Functoriality of the fiber operation on directed trees

```agda
module trees.functoriality-fiber-directed-tree where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import graph-theory.walks-directed-graphs

open import trees.directed-trees
open import trees.fibers-directed-trees
open import trees.morphisms-directed-trees
```

</details>

## Idea

Any morphism `f : S → T` of directed trees induces for any node `x ∈ S` a
morphism of fibers of directed trees.

## Definitions

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
      ( λ { e refl → refl})

  fiber-hom-Directed-Tree :
    hom-Directed-Tree
      ( fiber-Directed-Tree S x)
      ( fiber-Directed-Tree T (node-hom-Directed-Tree S T f x))
  pr1 fiber-hom-Directed-Tree = node-fiber-hom-Directed-Tree
  pr2 fiber-hom-Directed-Tree = edge-fiber-hom-Directed-Tree
```
