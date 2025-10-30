# Equivalences of dependent reflexive graphs

```agda
module graph-theory.equivalences-dependent-reflexive-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.families-of-equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import graph-theory.dependent-reflexive-graphs
open import graph-theory.equivalences-dependent-directed-graphs
open import graph-theory.reflexive-graphs
```

</details>

## Idea

Consider two
[dependent reflexive graphs](graph-theory.dependent-reflexive-graphs.md) `H` and
`K` over a [reflexive graph](graph-theory.reflexive-graphs.md) `G`. An
{{#concept "equivalence" Agda=equiv-Dependent-Reflexive-Graph}} from `H` to `K`
is an
[equivalence of dependent directed graphs](graph-theory.equivalences-dependent-directed-graphs.md)
from `H` to `K` preserving reflexivity. More specifically, an equivalence `α`
from `H` to `K` consists of

```text
  α₀ : (x : G₀) → H₀ x ≃ K₀ x
  α₁ : (x x' : G₀) (e : G₁ x x') (y : H₀ x) (y' : H₀ x') → H₁ e y y' ≃ K₁ e (α₀ y) (α₀ y')
  refl α : (x : G₀) (y : H₀ x) → α₁ (refl G x) (refl H y) ＝ refl K x (α₀ y).
```

## Definitions

### Equivalences of dependent directed graphs between dependent reflexive graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} {G : Reflexive-Graph l1 l2}
  (H : Dependent-Reflexive-Graph l3 l4 G)
  (K : Dependent-Reflexive-Graph l5 l6 G)
  where

  equiv-dependent-directed-graph-Dependent-Reflexive-Graph :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  equiv-dependent-directed-graph-Dependent-Reflexive-Graph =
    equiv-Dependent-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph H)
      ( dependent-directed-graph-Dependent-Reflexive-Graph K)

module _
  {l1 l2 l3 l4 l5 l6 : Level} {G : Reflexive-Graph l1 l2}
  (H : Dependent-Reflexive-Graph l3 l4 G)
  (K : Dependent-Reflexive-Graph l5 l6 G)
  (α : equiv-dependent-directed-graph-Dependent-Reflexive-Graph H K)
  where

  vertex-equiv-equiv-dependent-directed-graph-Dependent-Reflexive-Graph :
    fam-equiv
      ( vertex-Dependent-Reflexive-Graph H)
      ( vertex-Dependent-Reflexive-Graph K)
  vertex-equiv-equiv-dependent-directed-graph-Dependent-Reflexive-Graph =
    vertex-equiv-equiv-Dependent-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph H)
      ( dependent-directed-graph-Dependent-Reflexive-Graph K)
      ( α)

  vertex-equiv-dependent-directed-graph-Dependent-Reflexive-Graph :
    {x : vertex-Reflexive-Graph G} →
    vertex-Dependent-Reflexive-Graph H x →
    vertex-Dependent-Reflexive-Graph K x
  vertex-equiv-dependent-directed-graph-Dependent-Reflexive-Graph =
    vertex-equiv-Dependent-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph H)
      ( dependent-directed-graph-Dependent-Reflexive-Graph K)
      ( α)

  edge-equiv-equiv-dependent-directed-graph-Dependent-Reflexive-Graph :
    {x x' : vertex-Reflexive-Graph G}
    (e : edge-Reflexive-Graph G x x')
    (y : vertex-Dependent-Reflexive-Graph H x)
    (y' : vertex-Dependent-Reflexive-Graph H x') →
    edge-Dependent-Reflexive-Graph H e y y' ≃
    edge-Dependent-Reflexive-Graph K e
      ( vertex-equiv-dependent-directed-graph-Dependent-Reflexive-Graph y)
      ( vertex-equiv-dependent-directed-graph-Dependent-Reflexive-Graph y')
  edge-equiv-equiv-dependent-directed-graph-Dependent-Reflexive-Graph =
    edge-equiv-equiv-Dependent-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph H)
      ( dependent-directed-graph-Dependent-Reflexive-Graph K)
      ( α)

  edge-equiv-dependent-directed-graph-Dependent-Reflexive-Graph :
    {x x' : vertex-Reflexive-Graph G}
    {e : edge-Reflexive-Graph G x x'}
    {y : vertex-Dependent-Reflexive-Graph H x}
    {y' : vertex-Dependent-Reflexive-Graph H x'} →
    edge-Dependent-Reflexive-Graph H e y y' →
    edge-Dependent-Reflexive-Graph K e
      ( vertex-equiv-dependent-directed-graph-Dependent-Reflexive-Graph y)
      ( vertex-equiv-dependent-directed-graph-Dependent-Reflexive-Graph y')
  edge-equiv-dependent-directed-graph-Dependent-Reflexive-Graph =
    edge-equiv-Dependent-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph H)
      ( dependent-directed-graph-Dependent-Reflexive-Graph K)
      ( α)
```

### Equivalences of dependent reflexive graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} {G : Reflexive-Graph l1 l2}
  (H : Dependent-Reflexive-Graph l3 l4 G)
  (K : Dependent-Reflexive-Graph l5 l6 G)
  where

  equiv-Dependent-Reflexive-Graph : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  equiv-Dependent-Reflexive-Graph =
    Σ ( equiv-dependent-directed-graph-Dependent-Reflexive-Graph H K)
      ( λ (α₀ , α₁) →
        (x : vertex-Reflexive-Graph G)
        (y : vertex-Dependent-Reflexive-Graph H x) →
        map-equiv
          ( α₁ x x (refl-Reflexive-Graph G x) y y)
          ( refl-Dependent-Reflexive-Graph H y) ＝
        refl-Dependent-Reflexive-Graph K (map-equiv (α₀ x) y))

module _
  {l1 l2 l3 l4 l5 l6 : Level} {G : Reflexive-Graph l1 l2}
  (H : Dependent-Reflexive-Graph l3 l4 G)
  (K : Dependent-Reflexive-Graph l5 l6 G)
  (α : equiv-Dependent-Reflexive-Graph H K)
  where

  equiv-dependent-directed-graph-equiv-Dependent-Reflexive-Graph :
    equiv-dependent-directed-graph-Dependent-Reflexive-Graph H K
  equiv-dependent-directed-graph-equiv-Dependent-Reflexive-Graph = pr1 α

  vertex-equiv-equiv-Dependent-Reflexive-Graph :
    fam-equiv
      ( vertex-Dependent-Reflexive-Graph H)
      ( vertex-Dependent-Reflexive-Graph K)
  vertex-equiv-equiv-Dependent-Reflexive-Graph =
    vertex-equiv-equiv-Dependent-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph H)
      ( dependent-directed-graph-Dependent-Reflexive-Graph K)
      ( equiv-dependent-directed-graph-equiv-Dependent-Reflexive-Graph)

  vertex-equiv-Dependent-Reflexive-Graph :
    {x : vertex-Reflexive-Graph G} →
    vertex-Dependent-Reflexive-Graph H x →
    vertex-Dependent-Reflexive-Graph K x
  vertex-equiv-Dependent-Reflexive-Graph =
    vertex-equiv-Dependent-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph H)
      ( dependent-directed-graph-Dependent-Reflexive-Graph K)
      ( equiv-dependent-directed-graph-equiv-Dependent-Reflexive-Graph)

  edge-equiv-equiv-Dependent-Reflexive-Graph :
    {x x' : vertex-Reflexive-Graph G}
    (a : edge-Reflexive-Graph G x x')
    (y : vertex-Dependent-Reflexive-Graph H x)
    (y' : vertex-Dependent-Reflexive-Graph H x') →
    edge-Dependent-Reflexive-Graph H a y y' ≃
    edge-Dependent-Reflexive-Graph K a
      ( vertex-equiv-Dependent-Reflexive-Graph y)
      ( vertex-equiv-Dependent-Reflexive-Graph y')
  edge-equiv-equiv-Dependent-Reflexive-Graph =
    edge-equiv-equiv-Dependent-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph H)
      ( dependent-directed-graph-Dependent-Reflexive-Graph K)
      ( equiv-dependent-directed-graph-equiv-Dependent-Reflexive-Graph)

  edge-equiv-Dependent-Reflexive-Graph :
    {x x' : vertex-Reflexive-Graph G}
    {a : edge-Reflexive-Graph G x x'}
    {y : vertex-Dependent-Reflexive-Graph H x}
    {y' : vertex-Dependent-Reflexive-Graph H x'} →
    edge-Dependent-Reflexive-Graph H a y y' →
    edge-Dependent-Reflexive-Graph K a
      ( vertex-equiv-Dependent-Reflexive-Graph y)
      ( vertex-equiv-Dependent-Reflexive-Graph y')
  edge-equiv-Dependent-Reflexive-Graph =
    edge-equiv-Dependent-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph H)
      ( dependent-directed-graph-Dependent-Reflexive-Graph K)
      ( equiv-dependent-directed-graph-equiv-Dependent-Reflexive-Graph)

  refl-equiv-Dependent-Reflexive-Graph :
    {x : vertex-Reflexive-Graph G}
    (y : vertex-Dependent-Reflexive-Graph H x) →
    edge-equiv-Dependent-Reflexive-Graph (refl-Dependent-Reflexive-Graph H y) ＝
    refl-Dependent-Reflexive-Graph K (vertex-equiv-Dependent-Reflexive-Graph y)
  refl-equiv-Dependent-Reflexive-Graph = pr2 α _
```

### The identity equivalence of a dependent reflexive graph

```agda
module _
  {l1 l2 l3 l4 : Level} {G : Reflexive-Graph l1 l2}
  (H : Dependent-Reflexive-Graph l3 l4 G)
  where

  equiv-dependent-directed-graph-id-equiv-Dependent-Reflexive-Graph :
    equiv-dependent-directed-graph-Dependent-Reflexive-Graph H H
  equiv-dependent-directed-graph-id-equiv-Dependent-Reflexive-Graph =
    id-equiv-Dependent-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph H)

  vertex-equiv-id-equiv-Dependent-Reflexive-Graph :
    fam-equiv
      ( vertex-Dependent-Reflexive-Graph H)
      ( vertex-Dependent-Reflexive-Graph H)
  vertex-equiv-id-equiv-Dependent-Reflexive-Graph =
    vertex-equiv-equiv-dependent-directed-graph-Dependent-Reflexive-Graph
      ( H)
      ( H)
      ( equiv-dependent-directed-graph-id-equiv-Dependent-Reflexive-Graph)

  vertex-id-equiv-Dependent-Reflexive-Graph :
    {x : vertex-Reflexive-Graph G} →
    vertex-Dependent-Reflexive-Graph H x → vertex-Dependent-Reflexive-Graph H x
  vertex-id-equiv-Dependent-Reflexive-Graph =
    vertex-equiv-dependent-directed-graph-Dependent-Reflexive-Graph
      ( H)
      ( H)
      ( equiv-dependent-directed-graph-id-equiv-Dependent-Reflexive-Graph)

  edge-equiv-id-equiv-Dependent-Reflexive-Graph :
    {x x' : vertex-Reflexive-Graph G}
    (e : edge-Reflexive-Graph G x x')
    (y : vertex-Dependent-Reflexive-Graph H x)
    (y' : vertex-Dependent-Reflexive-Graph H x') →
    edge-Dependent-Reflexive-Graph H e y y' ≃
    edge-Dependent-Reflexive-Graph H e y y'
  edge-equiv-id-equiv-Dependent-Reflexive-Graph =
    edge-equiv-equiv-dependent-directed-graph-Dependent-Reflexive-Graph
      ( H)
      ( H)
      ( equiv-dependent-directed-graph-id-equiv-Dependent-Reflexive-Graph)

  edge-id-equiv-Dependent-Reflexive-Graph :
    {x x' : vertex-Reflexive-Graph G}
    {e : edge-Reflexive-Graph G x x'}
    {y : vertex-Dependent-Reflexive-Graph H x}
    {y' : vertex-Dependent-Reflexive-Graph H x'} →
    edge-Dependent-Reflexive-Graph H e y y' →
    edge-Dependent-Reflexive-Graph H e y y'
  edge-id-equiv-Dependent-Reflexive-Graph =
    edge-equiv-dependent-directed-graph-Dependent-Reflexive-Graph
      ( H)
      ( H)
      ( equiv-dependent-directed-graph-id-equiv-Dependent-Reflexive-Graph)

  refl-id-equiv-Dependent-Reflexive-Graph :
    {x : vertex-Reflexive-Graph G}
    (y : vertex-Dependent-Reflexive-Graph H x) →
    edge-id-equiv-Dependent-Reflexive-Graph
      ( refl-Dependent-Reflexive-Graph H y) ＝
    refl-Dependent-Reflexive-Graph H y
  refl-id-equiv-Dependent-Reflexive-Graph y = refl

  id-equiv-Dependent-Reflexive-Graph :
    equiv-Dependent-Reflexive-Graph H H
  pr1 id-equiv-Dependent-Reflexive-Graph =
    equiv-dependent-directed-graph-id-equiv-Dependent-Reflexive-Graph
  pr2 id-equiv-Dependent-Reflexive-Graph _ =
    refl-id-equiv-Dependent-Reflexive-Graph
```

## Properties

### Equivalences characterize identifications of dependent reflexive graphs

```agda
module _
  {l1 l2 l3 l4 : Level} {G : Reflexive-Graph l1 l2}
  (H : Dependent-Reflexive-Graph l3 l4 G)
  where

  abstract
    is-torsorial-equiv-Dependent-Reflexive-Graph :
      is-torsorial (equiv-Dependent-Reflexive-Graph {l5 = l3} {l6 = l4} H)
    is-torsorial-equiv-Dependent-Reflexive-Graph =
      is-torsorial-Eq-structure
        ( is-torsorial-equiv-Dependent-Directed-Graph
          ( dependent-directed-graph-Dependent-Reflexive-Graph H))
        ( dependent-directed-graph-Dependent-Reflexive-Graph H ,
          equiv-dependent-directed-graph-id-equiv-Dependent-Reflexive-Graph H)
        ( is-torsorial-Eq-Π (λ x → is-torsorial-htpy _))

  equiv-eq-Dependent-Reflexive-Graph :
    (K : Dependent-Reflexive-Graph l3 l4 G) →
    H ＝ K → equiv-Dependent-Reflexive-Graph H K
  equiv-eq-Dependent-Reflexive-Graph K refl =
    id-equiv-Dependent-Reflexive-Graph H

  abstract
    is-equiv-equiv-eq-Dependent-Reflexive-Graph :
      (K : Dependent-Reflexive-Graph l3 l4 G) →
      is-equiv (equiv-eq-Dependent-Reflexive-Graph K)
    is-equiv-equiv-eq-Dependent-Reflexive-Graph =
      fundamental-theorem-id
        is-torsorial-equiv-Dependent-Reflexive-Graph
        equiv-eq-Dependent-Reflexive-Graph

  extensionality-Dependent-Reflexive-Graph :
    (K : Dependent-Reflexive-Graph l3 l4 G) →
    (H ＝ K) ≃ equiv-Dependent-Reflexive-Graph H K
  pr1 (extensionality-Dependent-Reflexive-Graph K) =
    equiv-eq-Dependent-Reflexive-Graph K
  pr2 (extensionality-Dependent-Reflexive-Graph K) =
    is-equiv-equiv-eq-Dependent-Reflexive-Graph K

  eq-equiv-Dependent-Reflexive-Graph :
    (K : Dependent-Reflexive-Graph l3 l4 G) →
    equiv-Dependent-Reflexive-Graph H K → H ＝ K
  eq-equiv-Dependent-Reflexive-Graph K =
    map-inv-equiv (extensionality-Dependent-Reflexive-Graph K)
```
