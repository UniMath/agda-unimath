# Morphisms of reflexive graphs

```agda
module graph-theory.morphisms-reflexive-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.commuting-squares-of-identifications
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import graph-theory.morphisms-directed-graphs
open import graph-theory.reflexive-graphs
```

</details>

## Idea

A {{#concept "morphism of reflexive graphs" Agda=hom-Reflexive-Graph}} from `G` to `H` consists of a map `f₀ : G₀ → H₀` from the
vertices of `G` to the vertices of `H`, a family of maps `f₁` from the edges
`G₁ x y` in `G` to the edges `H₁ (f₀ x) (f₀ y)` in `H`, equipped with an [identification](foundation-core.identity-types.md)

```text
  fᵣ : f₁ (Gᵣ x) ＝ Hᵣ (f₀ x)
```

from the image of the reflexivity edge `Gᵣ x` to the reflexivity edge at `f₀ x` in `H`.

## Definitions

### Morphisms of reflexive graphs

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Reflexive-Graph l1 l2) (H : Reflexive-Graph l3 l4)
  where

  hom-Reflexive-Graph : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Reflexive-Graph =
    Σ ( hom-Directed-Graph
        ( directed-graph-Reflexive-Graph G)
        ( directed-graph-Reflexive-Graph H))
      ( λ (f₀ , f₁) →
        (x : vertex-Reflexive-Graph G) →
        f₁ x x (refl-Reflexive-Graph G x) ＝ refl-Reflexive-Graph H (f₀ x))

  module _
    (f : hom-Reflexive-Graph)
    where

    hom-directed-graph-hom-Reflexive-Graph :
      hom-Directed-Graph
        ( directed-graph-Reflexive-Graph G)
        ( directed-graph-Reflexive-Graph H)
    hom-directed-graph-hom-Reflexive-Graph = pr1 f

    vertex-hom-Reflexive-Graph :
      vertex-Reflexive-Graph G → vertex-Reflexive-Graph H
    vertex-hom-Reflexive-Graph =
      vertex-hom-Directed-Graph
        ( directed-graph-Reflexive-Graph G)
        ( directed-graph-Reflexive-Graph H)
        ( hom-directed-graph-hom-Reflexive-Graph)

    edge-hom-Reflexive-Graph :
      {x y : vertex-Reflexive-Graph G} (e : edge-Reflexive-Graph G x y) →
      edge-Reflexive-Graph H
        ( vertex-hom-Reflexive-Graph x)
        ( vertex-hom-Reflexive-Graph y)
    edge-hom-Reflexive-Graph =
      edge-hom-Directed-Graph
        ( directed-graph-Reflexive-Graph G)
        ( directed-graph-Reflexive-Graph H)
        ( hom-directed-graph-hom-Reflexive-Graph)

    refl-hom-Reflexive-Graph :
      (x : vertex-Reflexive-Graph G) →
      edge-hom-Reflexive-Graph (refl-Reflexive-Graph G x) ＝
      refl-Reflexive-Graph H (vertex-hom-Reflexive-Graph x)
    refl-hom-Reflexive-Graph = pr2 f
```

### Composition of morphisms graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (G : Reflexive-Graph l1 l2) (H : Reflexive-Graph l3 l4)
  (K : Reflexive-Graph l5 l6)
  (g : hom-Reflexive-Graph H K) (f : hom-Reflexive-Graph G H)
  where

  vertex-comp-hom-Reflexive-Graph :
    vertex-Reflexive-Graph G → vertex-Reflexive-Graph K
  vertex-comp-hom-Reflexive-Graph =
    (vertex-hom-Reflexive-Graph H K g) ∘ (vertex-hom-Reflexive-Graph G H f)

  edge-comp-hom-Reflexive-Graph :
    {x y : vertex-Reflexive-Graph G} →
    edge-Reflexive-Graph G x y →
    edge-Reflexive-Graph K
      ( vertex-comp-hom-Reflexive-Graph x)
      ( vertex-comp-hom-Reflexive-Graph y)
  edge-comp-hom-Reflexive-Graph e =
    edge-hom-Reflexive-Graph H K g (edge-hom-Reflexive-Graph G H f e)

  hom-directed-graph-comp-hom-Reflexive-Graph :
    hom-Directed-Graph
      ( directed-graph-Reflexive-Graph G)
      ( directed-graph-Reflexive-Graph K)
  pr1 hom-directed-graph-comp-hom-Reflexive-Graph =
    vertex-comp-hom-Reflexive-Graph
  pr2 hom-directed-graph-comp-hom-Reflexive-Graph _ _ =
    edge-comp-hom-Reflexive-Graph

  refl-comp-hom-Reflexive-Graph :
    (x : vertex-Reflexive-Graph G) →
    edge-comp-hom-Reflexive-Graph (refl-Reflexive-Graph G x) ＝
    refl-Reflexive-Graph K (vertex-comp-hom-Reflexive-Graph x)
  refl-comp-hom-Reflexive-Graph x =
    ( ap (edge-hom-Reflexive-Graph H K g) (refl-hom-Reflexive-Graph G H f _)) ∙
    ( refl-hom-Reflexive-Graph H K g _)

  comp-hom-Reflexive-Graph :
    hom-Reflexive-Graph G K
  pr1 comp-hom-Reflexive-Graph = hom-directed-graph-comp-hom-Reflexive-Graph
  pr2 comp-hom-Reflexive-Graph = refl-comp-hom-Reflexive-Graph
```

### Identity morphisms graphs

```agda
module _
  {l1 l2 : Level} (G : Reflexive-Graph l1 l2)
  where

  id-hom-Reflexive-Graph : hom-Reflexive-Graph G G
  pr1 id-hom-Reflexive-Graph = id-hom-Directed-Graph _
  pr2 id-hom-Reflexive-Graph _ = refl
```
