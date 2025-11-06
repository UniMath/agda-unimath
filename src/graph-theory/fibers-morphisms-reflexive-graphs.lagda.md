# Fibers of morphisms into reflexive graphs

```agda
module graph-theory.fibers-morphisms-reflexive-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.commuting-squares-of-identifications
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.families-of-equivalences
open import foundation.fibers-of-maps
open import foundation.identity-types
open import foundation.universe-levels

open import graph-theory.dependent-directed-graphs
open import graph-theory.dependent-reflexive-graphs
open import graph-theory.dependent-sums-reflexive-graphs
open import graph-theory.equivalences-dependent-directed-graphs
open import graph-theory.equivalences-dependent-reflexive-graphs
open import graph-theory.equivalences-reflexive-graphs
open import graph-theory.fibers-morphisms-directed-graphs
open import graph-theory.morphisms-reflexive-graphs
open import graph-theory.reflexive-graphs
```

</details>

## Idea

Consider a [morphism](graph-theory.morphisms-reflexive-graphs.md) `f : H → G` of
[reflexive graphs](graph-theory.reflexive-graphs.md). The
{{#concept "fiber" Disambiguation="morphisms of reflexive graphs" Agda=fiber-hom-Reflexive-Graph}}
of `f` is the
[dependent reflexive graph](graph-theory.dependent-reflexive-graphs.md) `fib_f`
over `G` given by

```text
  (fib_f)₀ x := fib f₀
  (fib_f)₁ e (y , refl) (y' , refl) := fib f₁ e
  refl (fib_f) (y , refl) := (refl H x , preserves-refl f x).
```

## Definitions

### The fiber of a morphism of reflexive graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (H : Reflexive-Graph l1 l2) (G : Reflexive-Graph l3 l4)
  (f : hom-Reflexive-Graph H G)
  where

  dependent-directed-graph-fiber-hom-Reflexive-Graph :
    Dependent-Directed-Graph
      ( l1 ⊔ l3)
      ( l2 ⊔ l4)
      ( directed-graph-Reflexive-Graph G)
  dependent-directed-graph-fiber-hom-Reflexive-Graph =
    fiber-hom-Directed-Graph
      ( directed-graph-Reflexive-Graph H)
      ( directed-graph-Reflexive-Graph G)
      ( hom-directed-graph-hom-Reflexive-Graph H G f)

  vertex-fiber-hom-Reflexive-Graph :
    vertex-Reflexive-Graph G → UU (l1 ⊔ l3)
  vertex-fiber-hom-Reflexive-Graph =
    vertex-Dependent-Directed-Graph
      dependent-directed-graph-fiber-hom-Reflexive-Graph

  edge-fiber-hom-Reflexive-Graph :
    {x x' : vertex-Reflexive-Graph G} (e : edge-Reflexive-Graph G x x') →
    vertex-fiber-hom-Reflexive-Graph x →
    vertex-fiber-hom-Reflexive-Graph x' → UU (l2 ⊔ l4)
  edge-fiber-hom-Reflexive-Graph =
    edge-Dependent-Directed-Graph
      dependent-directed-graph-fiber-hom-Reflexive-Graph

  refl-fiber-hom-Reflexive-Graph :
    {x : vertex-Reflexive-Graph G}
    (y : vertex-fiber-hom-Reflexive-Graph x) →
    edge-fiber-hom-Reflexive-Graph (refl-Reflexive-Graph G x) y y
  pr1 (refl-fiber-hom-Reflexive-Graph (y , refl)) =
    refl-Reflexive-Graph H y
  pr2 (refl-fiber-hom-Reflexive-Graph (y , refl)) =
    refl-hom-Reflexive-Graph H G f y

  fiber-hom-Reflexive-Graph :
    Dependent-Reflexive-Graph (l1 ⊔ l3) (l2 ⊔ l4) G
  pr1 fiber-hom-Reflexive-Graph =
    dependent-directed-graph-fiber-hom-Reflexive-Graph
  pr2 fiber-hom-Reflexive-Graph _ =
    refl-fiber-hom-Reflexive-Graph
```

## Properties

### The coproduct of the fibers of a morphism of reflexive graphs is the equivalent to the codomain

```agda
module _
  {l1 l2 l3 l4 : Level} (H : Reflexive-Graph l1 l2) (G : Reflexive-Graph l3 l4)
  (f : hom-Reflexive-Graph H G)
  where

  equiv-directed-graph-compute-Σ-fiber-hom-Reflexive-Graph :
    equiv-directed-graph-Reflexive-Graph
      ( H)
      ( Σ-Reflexive-Graph (fiber-hom-Reflexive-Graph H G f))
  equiv-directed-graph-compute-Σ-fiber-hom-Reflexive-Graph =
    compute-Σ-fiber-hom-Directed-Graph
      ( directed-graph-Reflexive-Graph H)
      ( directed-graph-Reflexive-Graph G)
      ( hom-directed-graph-hom-Reflexive-Graph H G f)

  vertex-compute-Σ-fiber-hom-Reflexive-Graph :
    vertex-Reflexive-Graph H →
    vertex-Σ-Reflexive-Graph (fiber-hom-Reflexive-Graph H G f)
  vertex-compute-Σ-fiber-hom-Reflexive-Graph =
    vertex-equiv-directed-graph-Reflexive-Graph H
      ( Σ-Reflexive-Graph (fiber-hom-Reflexive-Graph H G f))
      ( equiv-directed-graph-compute-Σ-fiber-hom-Reflexive-Graph)

  edge-compute-Σ-fiber-hom-Reflexive-graph :
    {x x' : vertex-Reflexive-Graph H} →
    edge-Reflexive-Graph H x x' →
    edge-Σ-Reflexive-Graph
      ( fiber-hom-Reflexive-Graph H G f)
      ( vertex-compute-Σ-fiber-hom-Reflexive-Graph x)
      ( vertex-compute-Σ-fiber-hom-Reflexive-Graph x')
  edge-compute-Σ-fiber-hom-Reflexive-graph =
    edge-equiv-directed-graph-Reflexive-Graph H
      ( Σ-Reflexive-Graph (fiber-hom-Reflexive-Graph H G f))
      ( equiv-directed-graph-compute-Σ-fiber-hom-Reflexive-Graph)

  refl-compute-Σ-fiber-hom-Reflexive-Graph :
    (x : vertex-Reflexive-Graph H) →
    edge-compute-Σ-fiber-hom-Reflexive-graph (refl-Reflexive-Graph H x) ＝
    refl-Σ-Reflexive-Graph
      ( fiber-hom-Reflexive-Graph H G f)
      ( vertex-compute-Σ-fiber-hom-Reflexive-Graph x)
  refl-compute-Σ-fiber-hom-Reflexive-Graph x =
    eq-pair-Σ
      ( refl-hom-Reflexive-Graph H G f x)
      ( ( inv
          ( compute-tr-fiber
            ( edge-hom-Reflexive-Graph H G f)
            ( refl-hom-Reflexive-Graph H G f x)
            ( _))) ∙
        ( refl))

  compute-Σ-fiber-hom-Reflexive-Graph :
    equiv-Reflexive-Graph
      ( H)
      ( Σ-Reflexive-Graph (fiber-hom-Reflexive-Graph H G f))
  pr1 compute-Σ-fiber-hom-Reflexive-Graph =
    equiv-directed-graph-compute-Σ-fiber-hom-Reflexive-Graph
  pr2 compute-Σ-fiber-hom-Reflexive-Graph =
    refl-compute-Σ-fiber-hom-Reflexive-Graph

  hom-compute-Σ-fiber-hom-Reflexive-Graph :
    hom-Reflexive-Graph
      ( H)
      ( Σ-Reflexive-Graph (fiber-hom-Reflexive-Graph H G f))
  hom-compute-Σ-fiber-hom-Reflexive-Graph =
    hom-equiv-Reflexive-Graph H
      ( Σ-Reflexive-Graph (fiber-hom-Reflexive-Graph H G f))
      ( compute-Σ-fiber-hom-Reflexive-Graph)
```

### The equivalence of the domain and the total graph of the fibers of a morphism of graphs fits in a commuting triangle

```agda
module _
  {l1 l2 l3 l4 : Level} (H : Reflexive-Graph l1 l2) (G : Reflexive-Graph l3 l4)
  (f : hom-Reflexive-Graph H G)
  where

  htpy-compute-Σ-fiber-hom-Reflexive-Graph :
    htpy-hom-Reflexive-Graph H G f
      ( comp-hom-Reflexive-Graph H
        ( Σ-Reflexive-Graph (fiber-hom-Reflexive-Graph H G f))
        ( G)
        ( pr1-Σ-Reflexive-Graph (fiber-hom-Reflexive-Graph H G f))
        ( hom-compute-Σ-fiber-hom-Reflexive-Graph H G f))
  pr1 htpy-compute-Σ-fiber-hom-Reflexive-Graph =
    htpy-compute-Σ-fiber-hom-Directed-Graph
      ( directed-graph-Reflexive-Graph H)
      ( directed-graph-Reflexive-Graph G)
      ( hom-directed-graph-hom-Reflexive-Graph H G f)
  pr2 htpy-compute-Σ-fiber-hom-Reflexive-Graph x =
    ap
      ( _∙ refl)
      ( ( ap-pr1-eq-pair-Σ
          ( refl-hom-Reflexive-Graph H G f x)
          ( _)) ∙
        ( inv (ap-id (refl-hom-Reflexive-Graph H G f x))))
```

### The fibers of the first projection of a dependent sums of reflexive graph

```agda
module _
  {l1 l2 l3 l4 : Level} {G : Reflexive-Graph l1 l2}
  (H : Dependent-Reflexive-Graph l3 l4 G)
  where

  fiber-pr1-Σ-Reflexive-Graph : Dependent-Reflexive-Graph (l1 ⊔ l3) (l2 ⊔ l4) G
  fiber-pr1-Σ-Reflexive-Graph =
    fiber-hom-Reflexive-Graph
      ( Σ-Reflexive-Graph H)
      ( G)
      ( pr1-Σ-Reflexive-Graph H)

  dependent-directed-graph-fiber-pr1-Σ-Reflexive-Graph :
    Dependent-Directed-Graph
      ( l1 ⊔ l3)
      ( l2 ⊔ l4)
      ( directed-graph-Reflexive-Graph G)
  dependent-directed-graph-fiber-pr1-Σ-Reflexive-Graph =
    dependent-directed-graph-Dependent-Reflexive-Graph
      fiber-pr1-Σ-Reflexive-Graph

  vertex-fiber-pr1-Σ-Reflexive-Graph :
    (x : vertex-Reflexive-Graph G) → UU (l1 ⊔ l3)
  vertex-fiber-pr1-Σ-Reflexive-Graph =
    vertex-Dependent-Reflexive-Graph fiber-pr1-Σ-Reflexive-Graph

  edge-fiber-pr1-Σ-Reflexive-Graph :
    {x x' : vertex-Reflexive-Graph G} →
    edge-Reflexive-Graph G x x' →
    vertex-fiber-pr1-Σ-Reflexive-Graph x →
    vertex-fiber-pr1-Σ-Reflexive-Graph x' → UU (l2 ⊔ l4)
  edge-fiber-pr1-Σ-Reflexive-Graph =
    edge-Dependent-Reflexive-Graph fiber-pr1-Σ-Reflexive-Graph

  refl-fiber-pr1-Σ-Reflexive-Graph :
    {x : vertex-Reflexive-Graph G} (y : vertex-fiber-pr1-Σ-Reflexive-Graph x) →
    edge-fiber-pr1-Σ-Reflexive-Graph (refl-Reflexive-Graph G x) y y
  refl-fiber-pr1-Σ-Reflexive-Graph =
    refl-Dependent-Reflexive-Graph fiber-pr1-Σ-Reflexive-Graph

  equiv-dependent-directed-graph-compute-fiber-pr1-Σ-Reflexive-Graph :
    equiv-Dependent-Directed-Graph
      ( dependent-directed-graph-fiber-pr1-Σ-Reflexive-Graph)
      ( dependent-directed-graph-Dependent-Reflexive-Graph H)
  equiv-dependent-directed-graph-compute-fiber-pr1-Σ-Reflexive-Graph =
    compute-fiber-pr1-Σ-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph H)

  vertex-equiv-compute-fiber-pr1-Σ-Reflexive-Graph :
    fam-equiv
      ( vertex-fiber-pr1-Σ-Reflexive-Graph)
      ( vertex-Dependent-Reflexive-Graph H)
  vertex-equiv-compute-fiber-pr1-Σ-Reflexive-Graph =
    vertex-equiv-compute-fiber-pr1-Σ-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph H)

  vertex-compute-fiber-pr1-Σ-Reflexive-Graph :
    {x : vertex-Reflexive-Graph G} →
    vertex-fiber-pr1-Σ-Reflexive-Graph x →
    vertex-Dependent-Reflexive-Graph H x
  vertex-compute-fiber-pr1-Σ-Reflexive-Graph =
    vertex-compute-fiber-pr1-Σ-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph H)

  edge-equiv-compute-fiber-pr1-Σ-Reflexive-Graph :
    {x x' : vertex-Reflexive-Graph G}
    (a : edge-Reflexive-Graph G x x') →
    (y : vertex-fiber-pr1-Σ-Reflexive-Graph x) →
    (y' : vertex-fiber-pr1-Σ-Reflexive-Graph x') →
    edge-fiber-pr1-Σ-Reflexive-Graph a y y' ≃
    edge-Dependent-Reflexive-Graph H a
      ( vertex-compute-fiber-pr1-Σ-Reflexive-Graph y)
      ( vertex-compute-fiber-pr1-Σ-Reflexive-Graph y')
  edge-equiv-compute-fiber-pr1-Σ-Reflexive-Graph =
    edge-equiv-compute-fiber-pr1-Σ-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph H)

  edge-compute-fiber-pr1-Σ-Reflexive-Graph :
    {x x' : vertex-Reflexive-Graph G}
    {a : edge-Reflexive-Graph G x x'} →
    {y : vertex-fiber-pr1-Σ-Reflexive-Graph x} →
    {y' : vertex-fiber-pr1-Σ-Reflexive-Graph x'} →
    edge-fiber-pr1-Σ-Reflexive-Graph a y y' →
    edge-Dependent-Reflexive-Graph H a
      ( vertex-compute-fiber-pr1-Σ-Reflexive-Graph y)
      ( vertex-compute-fiber-pr1-Σ-Reflexive-Graph y')
  edge-compute-fiber-pr1-Σ-Reflexive-Graph =
    edge-compute-fiber-pr1-Σ-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph H)

  refl-compute-fiber-pr1-Σ-Reflexive-Graph :
    {x : vertex-Reflexive-Graph G}
    (y : vertex-fiber-pr1-Σ-Reflexive-Graph x) →
    edge-compute-fiber-pr1-Σ-Reflexive-Graph
      ( refl-fiber-pr1-Σ-Reflexive-Graph y) ＝
    refl-Dependent-Reflexive-Graph H
      ( vertex-compute-fiber-pr1-Σ-Reflexive-Graph y)
  refl-compute-fiber-pr1-Σ-Reflexive-Graph ((x , y) , refl) =
    refl

  compute-fiber-pr1-Σ-Reflexive-Graph :
    equiv-Dependent-Reflexive-Graph fiber-pr1-Σ-Reflexive-Graph H
  pr1 compute-fiber-pr1-Σ-Reflexive-Graph =
    equiv-dependent-directed-graph-compute-fiber-pr1-Σ-Reflexive-Graph
  pr2 compute-fiber-pr1-Σ-Reflexive-Graph _ =
    refl-compute-fiber-pr1-Σ-Reflexive-Graph
```
