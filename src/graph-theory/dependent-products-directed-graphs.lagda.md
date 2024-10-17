# Dependent products of directed graphs

```agda
module graph-theory.dependent-products-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels

open import graph-theory.cartesian-products-directed-graphs
open import graph-theory.dependent-directed-graphs
open import graph-theory.directed-graphs
open import graph-theory.morphisms-directed-graphs
open import graph-theory.pullbacks-dependent-directed-graphs
open import graph-theory.sections-dependent-directed-graphs
```

</details>

## Idea

Given a [dependent directed graph](graph-theory.dependent-directed-graphs.md)
`B` over a [directed graphs](graph-theory.directed-graphs.md) `A`, the
{{#concept "dependent product" Disambiguation="directed graph" agda=Π-Directed-Graph}}
`Π A B` is the directed graph that satisfies the universal property

```text
  hom X (Π A B) ≃ hom (X × A) B.
```

Concretely, the directed graph `Π A B` has

- The type of functions `(x : A₀) → B₀ x` as its type of vertices
- For any two functions `f₀ g₀ : (x : A₀) → B₀ x`, an edge from `f₀` to `g₀` is
  an element of type

  ```text
    (x y : A₀) → A₁ x y → B₁ (f₀ x) (g₀ y).
  ```

The universal property of the dependent product gives that the type of
[sections](graph-theory.sections-dependent-directed-graphs.md) of `B` is
[equivalent](foundation-core.equivalences.md) to the type of morphisms from the
[terminal directed graph](graph-theory.terminal-directed-graphs.md) into
`Π A B`, which is in turn equivalent to the type of vertices `f₀` of the Π
`Π A B` equipped with a loop `(Π A B)₁ f f`. Indeed, this data consists of:

- A map `f₀ : A₀ → B₀`
- A family of maps `f₁ : (x y : A₀) → A₁ x y → B₁ (f₀ x) (f₀ y)`,

as expected for the type of sections of a dependent directed graph.

## Definitions

### The Π of directed graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Directed-Graph l1 l2)
  (B : Dependent-Directed-Graph l3 l4 A)
  where

  vertex-Π-Directed-Graph : UU (l1 ⊔ l3)
  vertex-Π-Directed-Graph =
    (x : vertex-Directed-Graph A) → vertex-Dependent-Directed-Graph B x

  edge-Π-Directed-Graph :
    (f g : vertex-Π-Directed-Graph) → UU (l1 ⊔ l2 ⊔ l4)
  edge-Π-Directed-Graph f g =
    (x y : vertex-Directed-Graph A) →
    (e : edge-Directed-Graph A x y) →
    edge-Dependent-Directed-Graph B {x} {y} e (f x) (g y)

  Π-Directed-Graph : Directed-Graph (l1 ⊔ l3) (l1 ⊔ l2 ⊔ l4)
  pr1 Π-Directed-Graph = vertex-Π-Directed-Graph
  pr2 Π-Directed-Graph = edge-Π-Directed-Graph
```

## Properties

### The Π directed graph satisfies the universal property of the Π

#### The evaluation of a morphism into an Π of directed graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Directed-Graph l1 l2) (B : Dependent-Directed-Graph l3 l4 A)
  (C : Directed-Graph l5 l6)
  (f : hom-Directed-Graph C (Π-Directed-Graph A B))
  where

  vertex-ev-section-Π-Directed-Graph :
    (x : vertex-product-Directed-Graph C A) →
    vertex-Dependent-Directed-Graph B (pr2 x)
  vertex-ev-section-Π-Directed-Graph (c , a) =
    vertex-hom-Directed-Graph C (Π-Directed-Graph A B) f c a

  edge-ev-section-Π-Directed-Graph :
    {x y : vertex-product-Directed-Graph C A} →
    (e : edge-product-Directed-Graph C A x y) →
    edge-Dependent-Directed-Graph B
      ( edge-pr2-product-Directed-Graph C A e)
      ( vertex-ev-section-Π-Directed-Graph x)
      ( vertex-ev-section-Π-Directed-Graph y)
  edge-ev-section-Π-Directed-Graph (d , e) =
    edge-hom-Directed-Graph C (Π-Directed-Graph A B) f d _ _ e

  ev-section-Π-Directed-Graph :
    section-Dependent-Directed-Graph
      ( pullback-Dependent-Directed-Graph
        ( product-Directed-Graph C A)
        ( pr2-product-Directed-Graph C A)
        ( B))
  pr1 ev-section-Π-Directed-Graph = vertex-ev-section-Π-Directed-Graph
  pr2 ev-section-Π-Directed-Graph = edge-ev-section-Π-Directed-Graph
```

#### Uncurrying a morphism from a cartesian product into a directed graph

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Directed-Graph l1 l2) (B : Dependent-Directed-Graph l3 l4 A)
  (C : Directed-Graph l5 l6)
  (f :
    section-Dependent-Directed-Graph
      ( pullback-Dependent-Directed-Graph
        ( product-Directed-Graph C A)
        ( pr2-product-Directed-Graph C A)
        ( B)))
  where

  vertex-uncurry-section-product-Directed-Graph :
    vertex-Directed-Graph C → vertex-Π-Directed-Graph A B
  vertex-uncurry-section-product-Directed-Graph c a =
    vertex-section-Dependent-Directed-Graph
      ( pullback-Dependent-Directed-Graph
        ( product-Directed-Graph C A)
        ( pr2-product-Directed-Graph C A)
        ( B))
      ( f)
      ( c , a)

  edge-uncurry-section-product-Directed-Graph :
    (x y : vertex-Directed-Graph C) →
    edge-Directed-Graph C x y →
    edge-Π-Directed-Graph A B
      ( vertex-uncurry-section-product-Directed-Graph x)
      ( vertex-uncurry-section-product-Directed-Graph y)
  edge-uncurry-section-product-Directed-Graph c c' d a a' e =
    edge-section-Dependent-Directed-Graph
      ( pullback-Dependent-Directed-Graph
        ( product-Directed-Graph C A)
        ( pr2-product-Directed-Graph C A)
        ( B))
      ( f)
      ( d , e)

  uncurry-section-product-Directed-Graph :
    hom-Directed-Graph C (Π-Directed-Graph A B)
  pr1 uncurry-section-product-Directed-Graph =
    vertex-uncurry-section-product-Directed-Graph
  pr2 uncurry-section-product-Directed-Graph =
    edge-uncurry-section-product-Directed-Graph
```

#### The equivalence of the adjunction between products and Πs of directed graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Directed-Graph l1 l2) (B : Dependent-Directed-Graph l3 l4 A)
  (C : Directed-Graph l5 l6)
  where

  htpy-is-section-uncurry-section-product-Directed-Graph :
    ( f :
      section-Dependent-Directed-Graph
        ( pullback-Dependent-Directed-Graph
          ( product-Directed-Graph C A)
          ( pr2-product-Directed-Graph C A)
          ( B))) →
    htpy-section-Dependent-Directed-Graph
      ( pullback-Dependent-Directed-Graph
        ( product-Directed-Graph C A)
        ( pr2-product-Directed-Graph C A)
        ( B))
      ( ev-section-Π-Directed-Graph A B C
        ( uncurry-section-product-Directed-Graph A B C f))
      ( f)
  pr1 (htpy-is-section-uncurry-section-product-Directed-Graph f) = refl-htpy
  pr2 (htpy-is-section-uncurry-section-product-Directed-Graph f) = refl-htpy

  is-section-uncurry-section-product-Directed-Graph :
    is-section
      ( ev-section-Π-Directed-Graph A B C)
      ( uncurry-section-product-Directed-Graph A B C)
  is-section-uncurry-section-product-Directed-Graph f =
    eq-htpy-section-Dependent-Directed-Graph
      ( pullback-Dependent-Directed-Graph
        ( product-Directed-Graph C A)
        ( pr2-product-Directed-Graph C A)
        ( B))
      ( ev-section-Π-Directed-Graph A B C
        ( uncurry-section-product-Directed-Graph A B C f))
      ( f)
      ( htpy-is-section-uncurry-section-product-Directed-Graph f)

  htpy-is-retraction-uncurry-section-product-Directed-Graph :
    (f : hom-Directed-Graph C (Π-Directed-Graph A B)) →
    htpy-hom-Directed-Graph
      ( C)
      ( Π-Directed-Graph A B)
      ( uncurry-section-product-Directed-Graph A B C
        ( ev-section-Π-Directed-Graph A B C f))
      ( f)
  pr1 (htpy-is-retraction-uncurry-section-product-Directed-Graph f) =
    refl-htpy
  pr2 (htpy-is-retraction-uncurry-section-product-Directed-Graph f) x y =
    refl-htpy

  is-retraction-uncurry-section-product-Directed-Graph :
    is-retraction
      ( ev-section-Π-Directed-Graph A B C)
      ( uncurry-section-product-Directed-Graph A B C)
  is-retraction-uncurry-section-product-Directed-Graph f =
    eq-htpy-hom-Directed-Graph
      ( C)
      ( Π-Directed-Graph A B)
      ( uncurry-section-product-Directed-Graph A B C
        ( ev-section-Π-Directed-Graph A B C f))
      ( f)
      ( htpy-is-retraction-uncurry-section-product-Directed-Graph f)

  is-equiv-ev-section-Π-Directed-Graph :
    is-equiv (ev-section-Π-Directed-Graph A B C)
  is-equiv-ev-section-Π-Directed-Graph =
    is-equiv-is-invertible
      ( uncurry-section-product-Directed-Graph A B C)
      ( is-section-uncurry-section-product-Directed-Graph)
      ( is-retraction-uncurry-section-product-Directed-Graph)

  ev-equiv-hom-Π-Directed-Graph :
    hom-Directed-Graph C (Π-Directed-Graph A B) ≃
    section-Dependent-Directed-Graph
      ( pullback-Dependent-Directed-Graph
        ( product-Directed-Graph C A)
        ( pr2-product-Directed-Graph C A)
        ( B))
  pr1 ev-equiv-hom-Π-Directed-Graph =
    ev-section-Π-Directed-Graph A B C
  pr2 ev-equiv-hom-Π-Directed-Graph =
    is-equiv-ev-section-Π-Directed-Graph
```

## See also

- [Dependent coproduct directed graphs](graph-theory.dependent-coproduct-directed-graphs.md)
