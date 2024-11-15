# Cartesian products of reflexive graphs

```agda
module graph-theory.cartesian-products-reflexive-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import graph-theory.cartesian-products-directed-graphs
open import graph-theory.directed-graphs
open import graph-theory.morphisms-directed-graphs
open import graph-theory.morphisms-reflexive-graphs
open import graph-theory.reflexive-graphs
```

</details>

## Idea

Consider two [reflexive graphs](graph-theory.reflexive-graphs.md)
`A := (A₀ , A₁)` and `B := (B₀ , B₁)`. The
{{#concept "cartesian product" Disambiguation="reflexive graphs" Agda=product-Reflexive-Graph}}
of `A` and `B` is the reflexive graph `A × B` given by

```text
  (A × B)₀ := A₀ × B₀
  (A × B)₁ (x , y) (x' , y') := A₁ x x' × B₁ y y'
  refl (A × B) (x , y) := (refl A x , refl B y).
```

## Definitions

### The cartesian product of reflexive graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Reflexive-Graph l1 l2) (B : Reflexive-Graph l3 l4)
  where

  directed-graph-product-Reflexive-Graph :
    Directed-Graph (l1 ⊔ l3) (l2 ⊔ l4)
  directed-graph-product-Reflexive-Graph =
    product-Directed-Graph
      ( directed-graph-Reflexive-Graph A)
      ( directed-graph-Reflexive-Graph B)

  vertex-product-Reflexive-Graph : UU (l1 ⊔ l3)
  vertex-product-Reflexive-Graph =
    vertex-Directed-Graph directed-graph-product-Reflexive-Graph

  edge-product-Reflexive-Graph :
    (x y : vertex-product-Reflexive-Graph) → UU (l2 ⊔ l4)
  edge-product-Reflexive-Graph =
    edge-Directed-Graph directed-graph-product-Reflexive-Graph

  refl-product-Reflexive-Graph :
    (x : vertex-product-Reflexive-Graph) → edge-product-Reflexive-Graph x x
  pr1 (refl-product-Reflexive-Graph (x , y)) = refl-Reflexive-Graph A x
  pr2 (refl-product-Reflexive-Graph (x , y)) = refl-Reflexive-Graph B y

  product-Reflexive-Graph :
    Reflexive-Graph (l1 ⊔ l3) (l2 ⊔ l4)
  pr1 product-Reflexive-Graph =
    directed-graph-product-Reflexive-Graph
  pr2 product-Reflexive-Graph =
    refl-product-Reflexive-Graph
```

### The projections out of cartesian products of reflexive graphs

#### The first projection out of the cartesian product of reflexive graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Reflexive-Graph l1 l2) (B : Reflexive-Graph l3 l4)
  where

  hom-directed-graph-pr1-product-Reflexive-Graph :
    hom-Directed-Graph
      ( directed-graph-product-Reflexive-Graph A B)
      ( directed-graph-Reflexive-Graph A)
  hom-directed-graph-pr1-product-Reflexive-Graph =
    pr1-product-Directed-Graph
      ( directed-graph-Reflexive-Graph A)
      ( directed-graph-Reflexive-Graph B)

  vertex-pr1-product-Reflexive-Graph :
    vertex-product-Reflexive-Graph A B → vertex-Reflexive-Graph A
  vertex-pr1-product-Reflexive-Graph =
    vertex-hom-Directed-Graph
      ( directed-graph-product-Reflexive-Graph A B)
      ( directed-graph-Reflexive-Graph A)
      ( hom-directed-graph-pr1-product-Reflexive-Graph)

  edge-pr1-product-Reflexive-Graph :
    {x y : vertex-product-Reflexive-Graph A B} →
    edge-product-Reflexive-Graph A B x y →
    edge-Reflexive-Graph A
      ( vertex-pr1-product-Reflexive-Graph x)
      ( vertex-pr1-product-Reflexive-Graph y)
  edge-pr1-product-Reflexive-Graph =
    edge-hom-Directed-Graph
      ( directed-graph-product-Reflexive-Graph A B)
      ( directed-graph-Reflexive-Graph A)
      ( hom-directed-graph-pr1-product-Reflexive-Graph)

  refl-pr1-product-Reflexive-Graph :
    (x : vertex-product-Reflexive-Graph A B) →
    edge-pr1-product-Reflexive-Graph (refl-product-Reflexive-Graph A B x) ＝
    refl-Reflexive-Graph A (vertex-pr1-product-Reflexive-Graph x)
  refl-pr1-product-Reflexive-Graph x = refl

  pr1-product-Reflexive-Graph :
    hom-Reflexive-Graph (product-Reflexive-Graph A B) A
  pr1 pr1-product-Reflexive-Graph =
    hom-directed-graph-pr1-product-Reflexive-Graph
  pr2 pr1-product-Reflexive-Graph =
    refl-pr1-product-Reflexive-Graph
```

#### The second projection out of the cartesian product of two reflexive graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Reflexive-Graph l1 l2) (B : Reflexive-Graph l3 l4)
  where

  hom-directed-graph-pr2-product-Reflexive-Graph :
    hom-Directed-Graph
      ( directed-graph-product-Reflexive-Graph A B)
      ( directed-graph-Reflexive-Graph B)
  hom-directed-graph-pr2-product-Reflexive-Graph =
    pr2-product-Directed-Graph
      ( directed-graph-Reflexive-Graph A)
      ( directed-graph-Reflexive-Graph B)

  vertex-pr2-product-Reflexive-Graph :
    vertex-product-Reflexive-Graph A B → vertex-Reflexive-Graph B
  vertex-pr2-product-Reflexive-Graph =
    vertex-hom-Directed-Graph
      ( directed-graph-product-Reflexive-Graph A B)
      ( directed-graph-Reflexive-Graph B)
      ( hom-directed-graph-pr2-product-Reflexive-Graph)

  edge-pr2-product-Reflexive-Graph :
    {x y : vertex-product-Reflexive-Graph A B} →
    edge-product-Reflexive-Graph A B x y →
    edge-Reflexive-Graph B
      ( vertex-pr2-product-Reflexive-Graph x)
      ( vertex-pr2-product-Reflexive-Graph y)
  edge-pr2-product-Reflexive-Graph =
    edge-hom-Directed-Graph
      ( directed-graph-product-Reflexive-Graph A B)
      ( directed-graph-Reflexive-Graph B)
      ( hom-directed-graph-pr2-product-Reflexive-Graph)

  refl-pr2-product-Reflexive-Graph :
    (x : vertex-product-Reflexive-Graph A B) →
    edge-pr2-product-Reflexive-Graph (refl-product-Reflexive-Graph A B x) ＝
    refl-Reflexive-Graph B (vertex-pr2-product-Reflexive-Graph x)
  refl-pr2-product-Reflexive-Graph x = refl

  pr2-product-Reflexive-Graph :
    hom-Reflexive-Graph (product-Reflexive-Graph A B) B
  pr1 pr2-product-Reflexive-Graph =
    hom-directed-graph-pr2-product-Reflexive-Graph
  pr2 pr2-product-Reflexive-Graph =
    refl-pr2-product-Reflexive-Graph
```
