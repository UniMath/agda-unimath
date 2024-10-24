# Sections of dependent reflexive graphs

```agda
module graph-theory.sections-dependent-reflexive-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-dependent-functions
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.commuting-squares-of-identifications
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.reflexive-relations
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import graph-theory.dependent-reflexive-graphs
open import graph-theory.reflexive-graphs
open import graph-theory.sections-dependent-directed-graphs
```

</details>

## Idea

Consider a
[dependent reflexive graph](graph-theory.dependent-reflexive-graphs.md) `B` over
a [reflexive graph](graph-theory.reflexive-graphs.md) `A`. A
{{#concept "section" Disambiguation="dependent reflexive graph" Agda=section-Dependent-Reflexive-Graph}}
`f` of `B` consists of

- A dependent function `f₀ : (x : A₀) → B₀ x`
- A family of dependent functions

  ```text
    f₁ : (e : A₁ x y) → B₁ e (f₀ x) (f₀ y)
  ```

  indexed by `x y : A₀`.

Note that [graph homomorphisms](graph-theory.morphisms-reflexive-graphs.md) from
`A` to `B` are sections of the constant dependent reflexive graph at `B` over
`A`.

## Definitions

### The type of sections of dependent directed graphs of a dependent reflexive graph

```agda
module _
  {l1 l2 l3 l4 : Level} {A : Reflexive-Graph l1 l2}
  (B : Dependent-Reflexive-Graph l3 l4 A)
  where

  section-dependent-directed-graph-Dependent-Reflexive-Graph :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  section-dependent-directed-graph-Dependent-Reflexive-Graph =
    section-Dependent-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph B)

  vertex-section-dependent-directed-graph-Dependent-Reflexive-Graph :
    section-dependent-directed-graph-Dependent-Reflexive-Graph →
    (x : vertex-Reflexive-Graph A) →
    vertex-Dependent-Reflexive-Graph B x
  vertex-section-dependent-directed-graph-Dependent-Reflexive-Graph =
    vertex-section-Dependent-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph B)

  edge-section-dependent-directed-graph-Dependent-Reflexive-Graph :
    (f : section-dependent-directed-graph-Dependent-Reflexive-Graph) →
    {x y : vertex-Reflexive-Graph A}
    (e : edge-Reflexive-Graph A x y) →
    edge-Dependent-Reflexive-Graph B e
      ( vertex-section-dependent-directed-graph-Dependent-Reflexive-Graph f x)
      ( vertex-section-dependent-directed-graph-Dependent-Reflexive-Graph f y)
  edge-section-dependent-directed-graph-Dependent-Reflexive-Graph =
    edge-section-Dependent-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph B)
```

### Sections of dependent reflexive graphs

```agda
module _
  {l1 l2 l3 l4 : Level} {A : Reflexive-Graph l1 l2}
  (B : Dependent-Reflexive-Graph l3 l4 A)
  where

  section-Dependent-Reflexive-Graph : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  section-Dependent-Reflexive-Graph =
    Σ ( section-dependent-directed-graph-Dependent-Reflexive-Graph B)
      ( λ f →
        ( x : vertex-Reflexive-Graph A) →
        edge-section-Dependent-Directed-Graph
          ( dependent-directed-graph-Dependent-Reflexive-Graph B)
          ( f)
          ( refl-Reflexive-Graph A x) ＝
        refl-Dependent-Reflexive-Graph B
          ( vertex-section-Dependent-Directed-Graph
            ( dependent-directed-graph-Dependent-Reflexive-Graph B)
            ( f)
            ( x)))
module _
  {l1 l2 l3 l4 : Level} {A : Reflexive-Graph l1 l2}
  (B : Dependent-Reflexive-Graph l3 l4 A)
  (f : section-Dependent-Reflexive-Graph B)
  where

  section-dependent-directed-graph-section-Dependent-Reflexive-Graph :
    section-dependent-directed-graph-Dependent-Reflexive-Graph B
  section-dependent-directed-graph-section-Dependent-Reflexive-Graph =
    pr1 f

  vertex-section-Dependent-Reflexive-Graph :
    (x : vertex-Reflexive-Graph A) →
    vertex-Dependent-Reflexive-Graph B x
  vertex-section-Dependent-Reflexive-Graph =
    vertex-section-Dependent-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph B)
      ( section-dependent-directed-graph-section-Dependent-Reflexive-Graph)

  edge-section-Dependent-Reflexive-Graph :
    {x y : vertex-Reflexive-Graph A} →
    (e : edge-Reflexive-Graph A x y) →
    edge-Dependent-Reflexive-Graph B e
      ( vertex-section-Dependent-Reflexive-Graph x)
      ( vertex-section-Dependent-Reflexive-Graph y)
  edge-section-Dependent-Reflexive-Graph =
    edge-section-Dependent-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph B)
      ( section-dependent-directed-graph-section-Dependent-Reflexive-Graph)

  refl-section-Dependent-Reflexive-Graph :
    (x : vertex-Reflexive-Graph A) →
    edge-section-Dependent-Reflexive-Graph
      ( refl-Reflexive-Graph A x) ＝
    refl-Dependent-Reflexive-Graph B
      ( vertex-section-Dependent-Reflexive-Graph x)
  refl-section-Dependent-Reflexive-Graph = pr2 f
```

### Homotopies of sections of dependent reflexive graphs

```agda
module _
  {l1 l2 l3 l4 : Level} {A : Reflexive-Graph l1 l2}
  (B : Dependent-Reflexive-Graph l3 l4 A)
  (f : section-Dependent-Reflexive-Graph B)
  where

  htpy-section-Dependent-Reflexive-Graph :
    section-Dependent-Reflexive-Graph B → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-section-Dependent-Reflexive-Graph g =
    Σ ( htpy-section-Dependent-Directed-Graph
        ( dependent-directed-graph-Dependent-Reflexive-Graph B)
        ( section-dependent-directed-graph-section-Dependent-Reflexive-Graph
          B f)
        ( section-dependent-directed-graph-section-Dependent-Reflexive-Graph
          B g))
      ( λ (H₀ , H₁) →
        (x : vertex-Reflexive-Graph A) →
        coherence-square-identifications
          ( ap
            ( binary-tr
              ( edge-Dependent-Reflexive-Graph B (refl-Reflexive-Graph A x))
              ( H₀ x)
              ( H₀ x))
            ( refl-section-Dependent-Reflexive-Graph B f x))
          ( H₁ (refl-Reflexive-Graph A x))
          ( binary-dependent-identification-refl-Reflexive-Relation
            ( edge-Dependent-Reflexive-Graph B (refl-Reflexive-Graph A x) ,
              refl-Dependent-Reflexive-Graph B)
            ( H₀ x))
          ( refl-section-Dependent-Reflexive-Graph B g x))

  refl-htpy-section-Dependent-Reflexive-Graph :
    htpy-section-Dependent-Reflexive-Graph f
  pr1 refl-htpy-section-Dependent-Reflexive-Graph =
    refl-htpy-section-Dependent-Directed-Graph
      ( dependent-directed-graph-Dependent-Reflexive-Graph B)
      ( section-dependent-directed-graph-section-Dependent-Reflexive-Graph B f)
  pr2 refl-htpy-section-Dependent-Reflexive-Graph x =
    inv (right-unit ∙ ap-id _)
```

## Properties

### Extensionality of sections of dependent reflexive graphs

```agda
module _
  {l1 l2 l3 l4 : Level} {A : Reflexive-Graph l1 l2}
  (B : Dependent-Reflexive-Graph l3 l4 A)
  (f : section-Dependent-Reflexive-Graph B)
  where

  abstract
    is-torsorial-htpy-section-Dependent-Reflexive-Graph :
      is-torsorial (htpy-section-Dependent-Reflexive-Graph B f)
    is-torsorial-htpy-section-Dependent-Reflexive-Graph =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy-section-Dependent-Directed-Graph
          ( dependent-directed-graph-Dependent-Reflexive-Graph B)
          ( section-dependent-directed-graph-section-Dependent-Reflexive-Graph
            ( B)
            ( f)))
        ( ( section-dependent-directed-graph-section-Dependent-Reflexive-Graph
            ( B)
            ( f)) ,
          ( refl-htpy-section-Dependent-Directed-Graph
            ( dependent-directed-graph-Dependent-Reflexive-Graph B)
            ( section-dependent-directed-graph-section-Dependent-Reflexive-Graph
              ( B)
              ( f))))
        ( is-torsorial-htpy' _)

  htpy-eq-section-Dependent-Reflexive-Graph :
    (g : section-Dependent-Reflexive-Graph B) →
    f ＝ g → htpy-section-Dependent-Reflexive-Graph B f g
  htpy-eq-section-Dependent-Reflexive-Graph g refl =
    refl-htpy-section-Dependent-Reflexive-Graph B f

  abstract
    is-equiv-htpy-eq-section-Dependent-Reflexive-Graph :
      (g : section-Dependent-Reflexive-Graph B) →
      is-equiv (htpy-eq-section-Dependent-Reflexive-Graph g)
    is-equiv-htpy-eq-section-Dependent-Reflexive-Graph =
      fundamental-theorem-id
        is-torsorial-htpy-section-Dependent-Reflexive-Graph
        htpy-eq-section-Dependent-Reflexive-Graph

  extensionality-section-Dependent-Reflexive-Graph :
    (g : section-Dependent-Reflexive-Graph B) →
    (f ＝ g) ≃ htpy-section-Dependent-Reflexive-Graph B f g
  pr1 (extensionality-section-Dependent-Reflexive-Graph g) =
    htpy-eq-section-Dependent-Reflexive-Graph g
  pr2 (extensionality-section-Dependent-Reflexive-Graph g) =
    is-equiv-htpy-eq-section-Dependent-Reflexive-Graph g

  eq-htpy-section-Dependent-Reflexive-Graph :
    (g : section-Dependent-Reflexive-Graph B) →
    htpy-section-Dependent-Reflexive-Graph B f g → f ＝ g
  eq-htpy-section-Dependent-Reflexive-Graph g =
    map-inv-equiv (extensionality-section-Dependent-Reflexive-Graph g)
```
