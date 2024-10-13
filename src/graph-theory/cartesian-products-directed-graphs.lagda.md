# Cartesian products of directed graphs

```agda
module graph-theory.cartesian-products-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.morphisms-directed-graphs
```

</details>

## Idea

Consider two [directed graphs](graph-theory.directed-graphs.md) `A := (A₀ , A₁)` and `B := (B₀ , B₁)`. The cartesian product of `A` and `B` is the directed graph `A × B` given by

```text
  (A × B)₀ := A₀ × B₀
  (A × B)₁ (x , y) (x' , y') := A₁ x x' × B₁ y y'.
```

## Definitions

### The cartesian product of directed graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Directed-Graph l1 l2) (B : Directed-Graph l3 l4)
  where

  vertex-product-Directed-Graph : UU (l1 ⊔ l3)
  vertex-product-Directed-Graph =
    vertex-Directed-Graph A × vertex-Directed-Graph B

  edge-product-Directed-Graph :
    (x y : vertex-product-Directed-Graph) → UU (l2 ⊔ l4)
  edge-product-Directed-Graph (x , y) (x' , y') =
    edge-Directed-Graph A x x' × edge-Directed-Graph B y y'

  product-Directed-Graph : Directed-Graph (l1 ⊔ l3) (l2 ⊔ l4)
  pr1 product-Directed-Graph = vertex-product-Directed-Graph
  pr2 product-Directed-Graph = edge-product-Directed-Graph
```

### The projections out of cartesian products of directed graphs

#### The first projection out of the cartesian product of directed graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Directed-Graph l1 l2) (B : Directed-Graph l3 l4)
  where

  vertex-pr1-product-Directed-Graph :
    vertex-product-Directed-Graph A B → vertex-Directed-Graph A
  vertex-pr1-product-Directed-Graph = pr1

  edge-pr1-product-Directed-Graph :
    {x y : vertex-product-Directed-Graph A B} →
    edge-product-Directed-Graph A B x y →
    edge-Directed-Graph A
      ( vertex-pr1-product-Directed-Graph x)
      ( vertex-pr1-product-Directed-Graph y)
  edge-pr1-product-Directed-Graph = pr1

  pr1-product-Directed-Graph :
    hom-Directed-Graph (product-Directed-Graph A B) A
  pr1 pr1-product-Directed-Graph = vertex-pr1-product-Directed-Graph
  pr2 pr1-product-Directed-Graph _ _ = edge-pr1-product-Directed-Graph
```

#### The second projection out of the cartesian product of two directed graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Directed-Graph l1 l2) (B : Directed-Graph l3 l4)
  where

  vertex-pr2-product-Directed-Graph :
    vertex-product-Directed-Graph A B → vertex-Directed-Graph B
  vertex-pr2-product-Directed-Graph = pr2

  edge-pr2-product-Directed-Graph :
    {x y : vertex-product-Directed-Graph A B} →
    edge-product-Directed-Graph A B x y →
    edge-Directed-Graph B
      ( vertex-pr2-product-Directed-Graph x)
      ( vertex-pr2-product-Directed-Graph y)
  edge-pr2-product-Directed-Graph = pr2

  pr2-product-Directed-Graph :
    hom-Directed-Graph (product-Directed-Graph A B) B
  pr1 pr2-product-Directed-Graph = vertex-pr2-product-Directed-Graph
  pr2 pr2-product-Directed-Graph _ _ = edge-pr2-product-Directed-Graph
```
