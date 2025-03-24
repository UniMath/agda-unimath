# Internal homs of directed graphs

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module graph-theory.internal-hom-directed-graphs
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.homotopies funext
open import foundation.retractions funext
open import foundation.sections funext
open import foundation.universe-levels

open import graph-theory.cartesian-products-directed-graphs funext univalence truncations
open import graph-theory.directed-graphs funext univalence
open import graph-theory.morphisms-directed-graphs funext univalence truncations
```

</details>

## Idea

Given two [directed graphs](graph-theory.directed-graphs.md) `A` and `B`, the
{{#concept "internal hom" Disambiguation="directed graph" agda=internal-hom-Directed-Graph}}
`B^A` is the directed graph that satisfies the universal property

```text
  hom X B^A ≃ hom (X × A) B.
```

Concretely, the directed graph `B^A` has

- The type of functions `A₀ → B₀` as its type of vertices
- For any two functions `f₀ g₀ : A₀ → B₀`, an edge from `f₀` to `g₀` is an
  element of type

  ```text
    (x y : A₀) → A₁ x y → B₁ (f₀ x) (g₀ y).
  ```

The universal property of the internal hom gives that the type of
[graph homomorphisms](graph-theory.morphisms-directed-graphs.md) `hom A B` is
[equivalent](foundation-core.equivalences.md) to the type of morphisms from the
[terminal directed graph](graph-theory.terminal-directed-graphs.md) into `B^A`,
which is in turn equivalent to the type of vertices `f₀` of the internal hom
`B^A` equipped with a loop `(B^A)₁ f f`. Indeed, this data consists of:

- A map `f₀ : A₀ → B₀`
- A family of maps `f₁ : (x y : A₀) → A₁ x y → B₁ (f₀ x) (f₀ y)`,

as expected for the type of morphisms of directed graphs.

## Definitions

### The internal hom of directed graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Directed-Graph l1 l2) (B : Directed-Graph l3 l4)
  where

  vertex-internal-hom-Directed-Graph : UU (l1 ⊔ l3)
  vertex-internal-hom-Directed-Graph =
    vertex-Directed-Graph A → vertex-Directed-Graph B

  edge-internal-hom-Directed-Graph :
    (f g : vertex-internal-hom-Directed-Graph) → UU (l1 ⊔ l2 ⊔ l4)
  edge-internal-hom-Directed-Graph f g =
    (x y : vertex-Directed-Graph A) →
    edge-Directed-Graph A x y → edge-Directed-Graph B (f x) (g y)

  internal-hom-Directed-Graph : Directed-Graph (l1 ⊔ l3) (l1 ⊔ l2 ⊔ l4)
  pr1 internal-hom-Directed-Graph = vertex-internal-hom-Directed-Graph
  pr2 internal-hom-Directed-Graph = edge-internal-hom-Directed-Graph
```

## Properties

### The internal hom directed graph satisfies the universal property of the internal hom

#### The evaluation of a morphism into an internal hom of directed graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Directed-Graph l1 l2) (B : Directed-Graph l3 l4)
  (C : Directed-Graph l5 l6)
  (f : hom-Directed-Graph C (internal-hom-Directed-Graph A B))
  where

  vertex-ev-hom-internal-hom-Directed-Graph :
    vertex-product-Directed-Graph C A → vertex-Directed-Graph B
  vertex-ev-hom-internal-hom-Directed-Graph (c , a) =
    vertex-hom-Directed-Graph C (internal-hom-Directed-Graph A B) f c a

  edge-ev-hom-internal-hom-Directed-Graph :
    (x y : vertex-product-Directed-Graph C A) →
    edge-product-Directed-Graph C A x y →
    edge-Directed-Graph B
      ( vertex-ev-hom-internal-hom-Directed-Graph x)
      ( vertex-ev-hom-internal-hom-Directed-Graph y)
  edge-ev-hom-internal-hom-Directed-Graph _ _ (d , e) =
    edge-hom-Directed-Graph C (internal-hom-Directed-Graph A B) f d _ _ e

  ev-hom-internal-hom-Directed-Graph :
    hom-Directed-Graph (product-Directed-Graph C A) B
  pr1 ev-hom-internal-hom-Directed-Graph =
    vertex-ev-hom-internal-hom-Directed-Graph
  pr2 ev-hom-internal-hom-Directed-Graph =
    edge-ev-hom-internal-hom-Directed-Graph
```

#### Uncurrying a morphism from a cartesian product into a directed graph

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Directed-Graph l1 l2) (B : Directed-Graph l3 l4)
  (C : Directed-Graph l5 l6)
  (f : hom-Directed-Graph (product-Directed-Graph C A) B)
  where

  vertex-uncurry-hom-product-Directed-Graph :
    vertex-Directed-Graph C → vertex-internal-hom-Directed-Graph A B
  vertex-uncurry-hom-product-Directed-Graph c a =
    vertex-hom-Directed-Graph (product-Directed-Graph C A) B f (c , a)

  edge-uncurry-hom-product-Directed-Graph :
    (x y : vertex-Directed-Graph C) →
    edge-Directed-Graph C x y →
    edge-internal-hom-Directed-Graph A B
      ( vertex-uncurry-hom-product-Directed-Graph x)
      ( vertex-uncurry-hom-product-Directed-Graph y)
  edge-uncurry-hom-product-Directed-Graph c c' d a a' e =
    edge-hom-Directed-Graph (product-Directed-Graph C A) B f (d , e)

  uncurry-hom-product-Directed-Graph :
    hom-Directed-Graph C (internal-hom-Directed-Graph A B)
  pr1 uncurry-hom-product-Directed-Graph =
    vertex-uncurry-hom-product-Directed-Graph
  pr2 uncurry-hom-product-Directed-Graph =
    edge-uncurry-hom-product-Directed-Graph
```

#### The equivalence of the adjunction between products and internal homs of directed graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Directed-Graph l1 l2) (B : Directed-Graph l3 l4)
  (C : Directed-Graph l5 l6)
  where

  htpy-is-section-uncurry-hom-product-Directed-Graph :
    (f : hom-Directed-Graph (product-Directed-Graph C A) B) →
    htpy-hom-Directed-Graph
      ( product-Directed-Graph C A)
      ( B)
      ( ev-hom-internal-hom-Directed-Graph A B C
        ( uncurry-hom-product-Directed-Graph A B C f))
      ( f)
  pr1 (htpy-is-section-uncurry-hom-product-Directed-Graph f) = refl-htpy
  pr2 (htpy-is-section-uncurry-hom-product-Directed-Graph f) x y = refl-htpy

  is-section-uncurry-hom-product-Directed-Graph :
    is-section
      ( ev-hom-internal-hom-Directed-Graph A B C)
      ( uncurry-hom-product-Directed-Graph A B C)
  is-section-uncurry-hom-product-Directed-Graph f =
    eq-htpy-hom-Directed-Graph
      ( product-Directed-Graph C A)
      ( B)
      ( ev-hom-internal-hom-Directed-Graph A B C
        ( uncurry-hom-product-Directed-Graph A B C f))
      ( f)
      ( htpy-is-section-uncurry-hom-product-Directed-Graph f)

  htpy-is-retraction-uncurry-hom-product-Directed-Graph :
    (f : hom-Directed-Graph C (internal-hom-Directed-Graph A B)) →
    htpy-hom-Directed-Graph
      ( C)
      ( internal-hom-Directed-Graph A B)
      ( uncurry-hom-product-Directed-Graph A B C
        ( ev-hom-internal-hom-Directed-Graph A B C f))
      ( f)
  pr1 (htpy-is-retraction-uncurry-hom-product-Directed-Graph f) = refl-htpy
  pr2 (htpy-is-retraction-uncurry-hom-product-Directed-Graph f) x y = refl-htpy

  is-retraction-uncurry-hom-product-Directed-Graph :
    is-retraction
      ( ev-hom-internal-hom-Directed-Graph A B C)
      ( uncurry-hom-product-Directed-Graph A B C)
  is-retraction-uncurry-hom-product-Directed-Graph f =
    eq-htpy-hom-Directed-Graph
      ( C)
      ( internal-hom-Directed-Graph A B)
      ( uncurry-hom-product-Directed-Graph A B C
        ( ev-hom-internal-hom-Directed-Graph A B C f))
      ( f)
      ( htpy-is-retraction-uncurry-hom-product-Directed-Graph f)

  is-equiv-ev-hom-internal-hom-Directed-Graph :
    is-equiv (ev-hom-internal-hom-Directed-Graph A B C)
  is-equiv-ev-hom-internal-hom-Directed-Graph =
    is-equiv-is-invertible
      ( uncurry-hom-product-Directed-Graph A B C)
      ( is-section-uncurry-hom-product-Directed-Graph)
      ( is-retraction-uncurry-hom-product-Directed-Graph)

  ev-equiv-hom-internal-hom-Directed-Graph :
    hom-Directed-Graph C (internal-hom-Directed-Graph A B) ≃
    hom-Directed-Graph (product-Directed-Graph C A) B
  pr1 ev-equiv-hom-internal-hom-Directed-Graph =
    ev-hom-internal-hom-Directed-Graph A B C
  pr2 ev-equiv-hom-internal-hom-Directed-Graph =
    is-equiv-ev-hom-internal-hom-Directed-Graph
```
