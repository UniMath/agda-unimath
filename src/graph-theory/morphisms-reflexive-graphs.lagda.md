# Morphisms of reflexive graphs

```agda
module graph-theory.morphisms-reflexive-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-dependent-functions
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

A
{{#concept "morphism" Disambiguation="of reflexive graphs" Agda=hom-Reflexive-Graph}}
of [reflexive graphs](graph-theory.reflexive-graphs.md) from `G` to `H` consists
of a map `f₀ : G₀ → H₀` from the vertices of `G` to the vertices of `H`, a
family of maps `f₁` from the edges `G₁ x y` in `G` to the edges
`H₁ (f₀ x) (f₀ y)` in `H`, equipped with an
[identification](foundation-core.identity-types.md)

```text
  preserves-refl f : f₁ (refl G x) ＝ refl H (f₀ x)
```

from the image of the reflexivity edge `refl G x` to the reflexivity edge at
`f₀ x` in `H`.

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

### Composition of morphisms of reflexive graphs

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

### Identity morphisms of reflexive graphs

```agda
module _
  {l1 l2 : Level} (G : Reflexive-Graph l1 l2)
  where

  id-hom-Reflexive-Graph : hom-Reflexive-Graph G G
  pr1 id-hom-Reflexive-Graph = id-hom-Directed-Graph _
  pr2 id-hom-Reflexive-Graph _ = refl
```

### Homotopies of morphisms of reflexive graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Reflexive-Graph l1 l2) (H : Reflexive-Graph l3 l4)
  (f g : hom-Reflexive-Graph G H)
  where

  htpy-hom-Reflexive-Graph : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-Reflexive-Graph =
    Σ ( htpy-hom-Directed-Graph
        ( directed-graph-Reflexive-Graph G)
        ( directed-graph-Reflexive-Graph H)
        ( hom-directed-graph-hom-Reflexive-Graph G H f)
        ( hom-directed-graph-hom-Reflexive-Graph G H g))
      ( λ (h₀ , h₁) →
        (x : vertex-Reflexive-Graph G) →
        coherence-square-identifications
          ( ap
            ( binary-tr (edge-Reflexive-Graph H) (h₀ x) (h₀ x))
            ( refl-hom-Reflexive-Graph G H f x))
          ( h₁ x x (refl-Reflexive-Graph G x))
          ( binary-dependent-identification-refl-Reflexive-Graph H (h₀ x))
          ( refl-hom-Reflexive-Graph G H g x))
```

### The reflexive homotopy of morphisms of reflexive graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Reflexive-Graph l1 l2) (H : Reflexive-Graph l3 l4)
  (f : hom-Reflexive-Graph G H)
  where

  refl-htpy-hom-Reflexive-Graph : htpy-hom-Reflexive-Graph G H f f
  pr1 refl-htpy-hom-Reflexive-Graph =
    refl-htpy-hom-Directed-Graph
      ( directed-graph-Reflexive-Graph G)
      ( directed-graph-Reflexive-Graph H)
      ( hom-directed-graph-hom-Reflexive-Graph G H f)
  pr2 refl-htpy-hom-Reflexive-Graph x =
    inv (right-unit ∙ ap-id _)
```

## Properties

### Extensionality of morphisms of reflexive graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Reflexive-Graph l1 l2) (H : Reflexive-Graph l3 l4)
  (f : hom-Reflexive-Graph G H)
  where

  is-torsorial-htpy-hom-Reflexive-Graph :
    is-torsorial (htpy-hom-Reflexive-Graph G H f)
  is-torsorial-htpy-hom-Reflexive-Graph =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy-hom-Directed-Graph
        ( directed-graph-Reflexive-Graph G)
        ( directed-graph-Reflexive-Graph H)
        ( hom-directed-graph-hom-Reflexive-Graph G H f))
      ( hom-directed-graph-hom-Reflexive-Graph G H f ,
        refl-htpy-hom-Directed-Graph
          ( directed-graph-Reflexive-Graph G)
          ( directed-graph-Reflexive-Graph H)
          ( hom-directed-graph-hom-Reflexive-Graph G H f))
      ( is-torsorial-htpy' _)

  htpy-eq-hom-Reflexive-Graph :
    (g : hom-Reflexive-Graph G H) →
    f ＝ g → htpy-hom-Reflexive-Graph G H f g
  htpy-eq-hom-Reflexive-Graph g refl =
    refl-htpy-hom-Reflexive-Graph G H f

  is-equiv-htpy-eq-hom-Reflexive-Graph :
    (g : hom-Reflexive-Graph G H) →
    is-equiv (htpy-eq-hom-Reflexive-Graph g)
  is-equiv-htpy-eq-hom-Reflexive-Graph =
    fundamental-theorem-id
      is-torsorial-htpy-hom-Reflexive-Graph
      htpy-eq-hom-Reflexive-Graph

  extensionality-hom-Reflexive-Graph :
    (g : hom-Reflexive-Graph G H) →
    (f ＝ g) ≃ htpy-hom-Reflexive-Graph G H f g
  pr1 (extensionality-hom-Reflexive-Graph g) =
    htpy-eq-hom-Reflexive-Graph g
  pr2 (extensionality-hom-Reflexive-Graph g) =
    is-equiv-htpy-eq-hom-Reflexive-Graph g

  eq-htpy-hom-Reflexive-Graph :
    (g : hom-Reflexive-Graph G H) →
    htpy-hom-Reflexive-Graph G H f g → f ＝ g
  eq-htpy-hom-Reflexive-Graph g =
    map-inv-equiv (extensionality-hom-Reflexive-Graph g)
```
