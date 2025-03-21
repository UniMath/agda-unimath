# Dependent sums reflexive graphs

```agda
module graph-theory.dependent-sums-reflexive-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import graph-theory.base-change-dependent-reflexive-graphs
open import graph-theory.dependent-reflexive-graphs
open import graph-theory.dependent-sums-directed-graphs
open import graph-theory.directed-graphs
open import graph-theory.discrete-dependent-reflexive-graphs
open import graph-theory.discrete-reflexive-graphs
open import graph-theory.morphisms-directed-graphs
open import graph-theory.morphisms-reflexive-graphs
open import graph-theory.reflexive-graphs
open import graph-theory.sections-dependent-directed-graphs
open import graph-theory.sections-dependent-reflexive-graphs
```

</details>

## Idea

Consider a
[dependent reflexive graph](graph-theory.dependent-reflexive-graphs.md) `H` over
a [reflexive graph](graph-theory.reflexive-graphs.md) `G`. The
{{#concept "dependent sum" Disambiguation="reflexive graphs" Agda=Σ-Reflexive-Graph}}
`Σ G H` is the reflexive graph given by

```text
  (Σ G H)₀ := Σ G₀ H₀
  (Σ G H)₁ (x , y) (x' , y') := Σ (e : G₁ x x') (H₁ e y y')
  refl (Σ G H) (x , y) := (refl G x , refl H y).
```

## Definitions

### The dependent sum of reflexive graphs

```agda
module _
  {l1 l2 l3 l4 : Level} {G : Reflexive-Graph l1 l2}
  (H : Dependent-Reflexive-Graph l3 l4 G)
  where

  directed-graph-Σ-Reflexive-Graph :
    Directed-Graph (l1 ⊔ l3) (l2 ⊔ l4)
  directed-graph-Σ-Reflexive-Graph =
    Σ-Directed-Graph (dependent-directed-graph-Dependent-Reflexive-Graph H)

  vertex-Σ-Reflexive-Graph : UU (l1 ⊔ l3)
  vertex-Σ-Reflexive-Graph =
    vertex-Directed-Graph directed-graph-Σ-Reflexive-Graph

  edge-Σ-Reflexive-Graph :
    (x y : vertex-Σ-Reflexive-Graph) → UU (l2 ⊔ l4)
  edge-Σ-Reflexive-Graph =
    edge-Directed-Graph directed-graph-Σ-Reflexive-Graph

  refl-Σ-Reflexive-Graph :
    (x : vertex-Σ-Reflexive-Graph) → edge-Σ-Reflexive-Graph x x
  pr1 (refl-Σ-Reflexive-Graph (x , y)) = refl-Reflexive-Graph G x
  pr2 (refl-Σ-Reflexive-Graph (x , y)) = refl-Dependent-Reflexive-Graph H y

  Σ-Reflexive-Graph : Reflexive-Graph (l1 ⊔ l3) (l2 ⊔ l4)
  pr1 Σ-Reflexive-Graph = directed-graph-Σ-Reflexive-Graph
  pr2 Σ-Reflexive-Graph = refl-Σ-Reflexive-Graph
```

### The first projection of the dependent sums of reflexive graph

```agda
module _
  {l1 l2 l3 l4 : Level} {G : Reflexive-Graph l1 l2}
  (H : Dependent-Reflexive-Graph l3 l4 G)
  where

  hom-directed-graph-pr1-Σ-Reflexive-Graph :
    hom-Directed-Graph
      ( directed-graph-Σ-Reflexive-Graph H)
      ( directed-graph-Reflexive-Graph G)
  hom-directed-graph-pr1-Σ-Reflexive-Graph =
    pr1-Σ-Directed-Graph (dependent-directed-graph-Dependent-Reflexive-Graph H)

  vertex-pr1-Σ-Reflexive-Graph :
    vertex-Σ-Reflexive-Graph H → vertex-Reflexive-Graph G
  vertex-pr1-Σ-Reflexive-Graph =
    vertex-hom-Directed-Graph
      ( directed-graph-Σ-Reflexive-Graph H)
      ( directed-graph-Reflexive-Graph G)
      ( hom-directed-graph-pr1-Σ-Reflexive-Graph)

  edge-pr1-Σ-Reflexive-Graph :
    {x y : vertex-Σ-Reflexive-Graph H} →
    edge-Σ-Reflexive-Graph H x y →
    edge-Reflexive-Graph G
      ( vertex-pr1-Σ-Reflexive-Graph x)
      ( vertex-pr1-Σ-Reflexive-Graph y)
  edge-pr1-Σ-Reflexive-Graph =
    edge-hom-Directed-Graph
      ( directed-graph-Σ-Reflexive-Graph H)
      ( directed-graph-Reflexive-Graph G)
      ( hom-directed-graph-pr1-Σ-Reflexive-Graph)

  refl-pr1-Σ-Reflexive-Graph :
    (x : vertex-Σ-Reflexive-Graph H) →
    edge-pr1-Σ-Reflexive-Graph (refl-Σ-Reflexive-Graph H x) ＝
    refl-Reflexive-Graph G (vertex-pr1-Σ-Reflexive-Graph x)
  refl-pr1-Σ-Reflexive-Graph x = refl

  pr1-Σ-Reflexive-Graph : hom-Reflexive-Graph (Σ-Reflexive-Graph H) G
  pr1 pr1-Σ-Reflexive-Graph = hom-directed-graph-pr1-Σ-Reflexive-Graph
  pr2 pr1-Σ-Reflexive-Graph = refl-pr1-Σ-Reflexive-Graph
```

### The second projection of the dependent sums of reflexive graph

```agda
module _
  {l1 l2 l3 l4 : Level} {G : Reflexive-Graph l1 l2}
  (H : Dependent-Reflexive-Graph l3 l4 G)
  where

  section-dependent-directed-graph-pr2-Σ-Reflexive-Graph :
    section-dependent-directed-graph-Dependent-Reflexive-Graph
      ( base-change-Dependent-Reflexive-Graph
        ( Σ-Reflexive-Graph H)
        ( pr1-Σ-Reflexive-Graph H)
        ( H))
  section-dependent-directed-graph-pr2-Σ-Reflexive-Graph =
    pr2-Σ-Directed-Graph (dependent-directed-graph-Dependent-Reflexive-Graph H)

  vertex-pr2-Σ-Reflexive-Graph :
    (x : vertex-Σ-Reflexive-Graph H) →
    vertex-base-change-Dependent-Reflexive-Graph
      ( Σ-Reflexive-Graph H)
      ( pr1-Σ-Reflexive-Graph H)
      ( H)
      ( x)
  vertex-pr2-Σ-Reflexive-Graph =
    vertex-section-dependent-directed-graph-Dependent-Reflexive-Graph
      ( base-change-Dependent-Reflexive-Graph
        ( Σ-Reflexive-Graph H)
        ( pr1-Σ-Reflexive-Graph H)
        ( H))
      ( section-dependent-directed-graph-pr2-Σ-Reflexive-Graph)

  edge-pr2-Σ-Reflexive-Graph :
    {x y : vertex-Σ-Reflexive-Graph H}
    (e : edge-Σ-Reflexive-Graph H x y) →
    edge-base-change-Dependent-Reflexive-Graph
      ( Σ-Reflexive-Graph H)
      ( pr1-Σ-Reflexive-Graph H)
      ( H)
      ( e)
      ( vertex-pr2-Σ-Reflexive-Graph x)
      ( vertex-pr2-Σ-Reflexive-Graph y)
  edge-pr2-Σ-Reflexive-Graph =
    edge-section-dependent-directed-graph-Dependent-Reflexive-Graph
      ( base-change-Dependent-Reflexive-Graph
        ( Σ-Reflexive-Graph H)
        ( pr1-Σ-Reflexive-Graph H)
        ( H))
      ( section-dependent-directed-graph-pr2-Σ-Reflexive-Graph)

  refl-pr2-Σ-Reflexive-Graph :
    (x : vertex-Σ-Reflexive-Graph H) →
    edge-pr2-Σ-Reflexive-Graph (refl-Σ-Reflexive-Graph H x) ＝
    refl-Dependent-Reflexive-Graph H (vertex-pr2-Σ-Reflexive-Graph x)
  refl-pr2-Σ-Reflexive-Graph x = refl

  pr2-Σ-Reflexive-Graph :
    section-Dependent-Reflexive-Graph
      ( base-change-Dependent-Reflexive-Graph
        ( Σ-Reflexive-Graph H)
        ( pr1-Σ-Reflexive-Graph H)
        ( H))
  pr1 pr2-Σ-Reflexive-Graph =
    section-dependent-directed-graph-pr2-Σ-Reflexive-Graph
  pr2 pr2-Σ-Reflexive-Graph =
    refl-pr2-Σ-Reflexive-Graph
```

## Properties

### Discreteness of dependent sum reflexive graphs

If `G` is a discrete reflexive graph and `H` is a dependent reflexive graph over
`G`, then `H` is discrete if and only if the
[dependent sum graph](graph-theory.dependent-sums-reflexive-graphs.md) `Σ G H`
is a discrete reflexive graph.

```agda
module _
  {l1 l2 l3 l4 : Level} {G : Reflexive-Graph l1 l2}
  (H : Dependent-Reflexive-Graph l3 l4 G)
  where

  abstract
    is-discrete-Σ-is-discrete-Dependent-Reflexive-Graph :
      is-discrete-Reflexive-Graph G →
      is-discrete-Dependent-Reflexive-Graph H →
      is-discrete-Reflexive-Graph (Σ-Reflexive-Graph H)
    is-discrete-Σ-is-discrete-Dependent-Reflexive-Graph d c (x , y) =
      is-torsorial-Eq-structure
        ( d x)
        ( x , refl-Reflexive-Graph G x)
        ( c x y)

  abstract
    is-discrete-is-discrete-Σ-Reflexive-Graph :
      is-discrete-Reflexive-Graph G →
      is-discrete-Reflexive-Graph (Σ-Reflexive-Graph H) →
      is-discrete-Dependent-Reflexive-Graph H
    is-discrete-is-discrete-Σ-Reflexive-Graph d c x y =
      is-contr-equiv'
        ( Σ ( Σ ( vertex-Reflexive-Graph G)
                ( vertex-Dependent-Reflexive-Graph H))
            ( λ (x' , y') →
              Σ ( edge-Reflexive-Graph G x x')
                ( λ e → edge-Dependent-Reflexive-Graph H e y y')))
        ( left-unit-law-Σ-is-contr (d x) (x , refl-Reflexive-Graph G x) ∘e
          interchange-Σ-Σ (λ x' y' e → edge-Dependent-Reflexive-Graph H e y y'))
        ( c (x , y))
```

## See also

- [Dependent product reflexive graphs](graph-theory.dependent-products-reflexive-graphs.md)
