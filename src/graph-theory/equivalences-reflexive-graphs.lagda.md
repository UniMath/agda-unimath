# Equivalences of reflexive graphs

```agda
module graph-theory.equivalences-reflexive-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import graph-theory.equivalences-directed-graphs
open import graph-theory.morphisms-reflexive-graphs
open import graph-theory.reflexive-graphs
```

</details>

## Idea

An
{{#concept "equivalence" Disambiguation="of reflexive graphs" WD="graph isomorphism" WDID=Q303100 Agda=equiv-Reflexive-Graph}}
of [reflexive graphs](graph-theory.reflexive-graphs.md) from `(V, E, r)` to
`(V', E', r')` consists of an
[equivalence](graph-theory.equivalences-directed-graphs.md) `(e₀, e₁)` of
[directed graphs](graph-theory.directed-graphs.md) from `(V, E)` to `(V', E')`
equipped with an [identification](foundation-core.identity-types.md)

```text
  e₁ (r x) ＝ r' (e₀ x)
```

for each `x : V`. More specifically, an equivalence of reflexive graphs consists
of an [equivalence](foundation-core.equivalences.md) `e₀ : V ≃ V'` of vertices,
a family of equivalences `e₁ : E x y ≃ E' (e x) (e y)` of edges indexed by
`x y : V`, and a family of identifications

```text
  e₁ (r x) ＝ r' (e₀ x)
```

indexed by `x : V`.

## Definitions

### Equivalences of directed graphs between reflexive graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Reflexive-Graph l1 l2) (H : Reflexive-Graph l3 l4)
  where

  equiv-directed-graph-Reflexive-Graph : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-directed-graph-Reflexive-Graph =
    equiv-Directed-Graph
      ( directed-graph-Reflexive-Graph G)
      ( directed-graph-Reflexive-Graph H)

module _
  {l1 l2 l3 l4 : Level} (G : Reflexive-Graph l1 l2) (H : Reflexive-Graph l3 l4)
  (e : equiv-directed-graph-Reflexive-Graph G H)
  where

  vertex-equiv-equiv-directed-graph-Reflexive-Graph :
    vertex-Reflexive-Graph G ≃ vertex-Reflexive-Graph H
  vertex-equiv-equiv-directed-graph-Reflexive-Graph =
    vertex-equiv-equiv-Directed-Graph
      ( directed-graph-Reflexive-Graph G)
      ( directed-graph-Reflexive-Graph H)
      ( e)

  vertex-equiv-directed-graph-Reflexive-Graph :
    vertex-Reflexive-Graph G → vertex-Reflexive-Graph H
  vertex-equiv-directed-graph-Reflexive-Graph =
    vertex-equiv-Directed-Graph
      ( directed-graph-Reflexive-Graph G)
      ( directed-graph-Reflexive-Graph H)
      ( e)

  edge-equiv-equiv-directed-graph-Reflexive-Graph :
    (x x' : vertex-Reflexive-Graph G) →
    edge-Reflexive-Graph G x x' ≃
    edge-Reflexive-Graph H
      ( vertex-equiv-directed-graph-Reflexive-Graph x)
      ( vertex-equiv-directed-graph-Reflexive-Graph x')
  edge-equiv-equiv-directed-graph-Reflexive-Graph =
    edge-equiv-equiv-Directed-Graph
      ( directed-graph-Reflexive-Graph G)
      ( directed-graph-Reflexive-Graph H)
      ( e)

  edge-equiv-directed-graph-Reflexive-Graph :
    {x x' : vertex-Reflexive-Graph G} →
    edge-Reflexive-Graph G x x' →
    edge-Reflexive-Graph H
      ( vertex-equiv-directed-graph-Reflexive-Graph x)
      ( vertex-equiv-directed-graph-Reflexive-Graph x')
  edge-equiv-directed-graph-Reflexive-Graph =
    edge-equiv-Directed-Graph
      ( directed-graph-Reflexive-Graph G)
      ( directed-graph-Reflexive-Graph H)
      ( e)
```

### Equivalences of reflexive graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Reflexive-Graph l1 l2) (H : Reflexive-Graph l3 l4)
  where

  equiv-Reflexive-Graph : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-Reflexive-Graph =
    Σ ( equiv-directed-graph-Reflexive-Graph G H)
      ( λ e →
        (x : vertex-Reflexive-Graph G) →
        edge-equiv-directed-graph-Reflexive-Graph G H e
          ( refl-Reflexive-Graph G x) ＝
        refl-Reflexive-Graph H
          (vertex-equiv-directed-graph-Reflexive-Graph G H e x))

module _
  {l1 l2 l3 l4 : Level} (G : Reflexive-Graph l1 l2) (H : Reflexive-Graph l3 l4)
  (e : equiv-Reflexive-Graph G H)
  where

  equiv-directed-graph-equiv-Reflexive-Graph :
    equiv-directed-graph-Reflexive-Graph G H
  equiv-directed-graph-equiv-Reflexive-Graph = pr1 e

  vertex-equiv-equiv-Reflexive-Graph :
    vertex-Reflexive-Graph G ≃ vertex-Reflexive-Graph H
  vertex-equiv-equiv-Reflexive-Graph =
    vertex-equiv-equiv-directed-graph-Reflexive-Graph G H
      equiv-directed-graph-equiv-Reflexive-Graph

  vertex-equiv-Reflexive-Graph :
    vertex-Reflexive-Graph G → vertex-Reflexive-Graph H
  vertex-equiv-Reflexive-Graph =
    vertex-equiv-directed-graph-Reflexive-Graph G H
      equiv-directed-graph-equiv-Reflexive-Graph

  edge-equiv-equiv-Reflexive-Graph :
    (x x' : vertex-Reflexive-Graph G) →
    edge-Reflexive-Graph G x x' ≃
    edge-Reflexive-Graph H
      ( vertex-equiv-Reflexive-Graph x)
      ( vertex-equiv-Reflexive-Graph x')
  edge-equiv-equiv-Reflexive-Graph =
    edge-equiv-equiv-directed-graph-Reflexive-Graph G H
      equiv-directed-graph-equiv-Reflexive-Graph

  edge-equiv-Reflexive-Graph :
    {x x' : vertex-Reflexive-Graph G} →
    edge-Reflexive-Graph G x x' →
    edge-Reflexive-Graph H
      ( vertex-equiv-Reflexive-Graph x)
      ( vertex-equiv-Reflexive-Graph x')
  edge-equiv-Reflexive-Graph =
    edge-equiv-directed-graph-Reflexive-Graph G H
      equiv-directed-graph-equiv-Reflexive-Graph

  refl-equiv-Reflexive-Graph :
    (x : vertex-Reflexive-Graph G) →
    edge-equiv-Reflexive-Graph (refl-Reflexive-Graph G x) ＝
    refl-Reflexive-Graph H (vertex-equiv-Reflexive-Graph x)
  refl-equiv-Reflexive-Graph = pr2 e

  hom-equiv-Reflexive-Graph :
    hom-Reflexive-Graph G H
  pr1 (pr1 hom-equiv-Reflexive-Graph) = vertex-equiv-Reflexive-Graph
  pr2 (pr1 hom-equiv-Reflexive-Graph) _ _ = edge-equiv-Reflexive-Graph
  pr2 hom-equiv-Reflexive-Graph = refl-equiv-Reflexive-Graph
```
