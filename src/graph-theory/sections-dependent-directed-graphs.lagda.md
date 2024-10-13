# Sections of dependent directed graphs

```agda
module graph-theory.sections-dependent-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import graph-theory.dependent-directed-graphs
open import graph-theory.directed-graphs
```

</details>

## Idea

Consider a [dependent directed graph](graph-theory.dependent-directed-graphs.md) `B` over a [directed graph](graph-theory.directed-graphs.md) `A`. A {{#concept "section" Disambiguation="dependent directed graph" Agda=section-Dependent-Directed-Graph}} `f` of `B` consists of

- A dependent function `f₀ : (x : A₀) → B₀ x`
- A family of dependent functions

  ```text
    f₁ : (e : A₁ x y) → B₁ e (f₀ x) (f₀ y)
  ```

  indexed by `x y : A₀`.

Note that [graph homomorphisms](graph-theory.morphisms-directed-graphs.md) from `A` to `B` are sections of the constant dependent directed graph at `B` over `A`.

## Definitions

### Sections of dependent directed graphs

```agda
module _
  {l1 l2 l3 l4 : Level} {A : Directed-Graph l1 l2}
  (B : Dependent-Directed-Graph l3 l4 A)
  where

  section-Dependent-Directed-Graph : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  section-Dependent-Directed-Graph =
    Σ ( (x : vertex-Directed-Graph A) → vertex-Dependent-Directed-Graph B x)
      ( λ f₀ →
        {x y : vertex-Directed-Graph A} (e : edge-Directed-Graph A x y) →
        edge-Dependent-Directed-Graph B e (f₀ x) (f₀ y))

module _
  {l1 l2 l3 l4 : Level} {A : Directed-Graph l1 l2}
  (B : Dependent-Directed-Graph l3 l4 A)
  (f : section-Dependent-Directed-Graph B)
  where

  vertex-section-Dependent-Directed-Graph :
    (x : vertex-Directed-Graph A) → vertex-Dependent-Directed-Graph B x
  vertex-section-Dependent-Directed-Graph =
    pr1 f

  edge-section-Dependent-Directed-Graph :
    {x y : vertex-Directed-Graph A} →
    (e : edge-Directed-Graph A x y) →
    edge-Dependent-Directed-Graph B e
      ( vertex-section-Dependent-Directed-Graph x)
      ( vertex-section-Dependent-Directed-Graph y)
  edge-section-Dependent-Directed-Graph =
    pr2 f
```

### Homotopies of sections of dependent directed graphs

```agda
module _
  {l1 l2 l3 l4 : Level} {A : Directed-Graph l1 l2}
  (B : Dependent-Directed-Graph l3 l4 A)
  (f : section-Dependent-Directed-Graph B)
  where

  htpy-section-Dependent-Directed-Graph :
    section-Dependent-Directed-Graph B → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-section-Dependent-Directed-Graph g =
    Σ ( vertex-section-Dependent-Directed-Graph B f ~
        vertex-section-Dependent-Directed-Graph B g)
      ( λ H₀ →
        {x y : vertex-Directed-Graph A} (e : edge-Directed-Graph A x y) →
        tr
          ( edge-Dependent-Directed-Graph B e _)
          ( H₀ y)
          ( tr
            ( λ u → edge-Dependent-Directed-Graph B e u _)
            ( H₀ x)
            ( edge-section-Dependent-Directed-Graph B f e)) ＝
        edge-section-Dependent-Directed-Graph B g e)

  refl-htpy-section-Dependent-Directed-Graph :
    htpy-section-Dependent-Directed-Graph f
  pr1 refl-htpy-section-Dependent-Directed-Graph = refl-htpy
  pr2 refl-htpy-section-Dependent-Directed-Graph = refl-htpy
```

## Properties

### Extensionality of sections of dependent directed graphs

```agda
module _
  {l1 l2 l3 l4 : Level} {A : Directed-Graph l1 l2}
  (B : Dependent-Directed-Graph l3 l4 A)
  (f : section-Dependent-Directed-Graph B)
  where

  abstract
    is-torsorial-htpy-section-Dependent-Directed-Graph :
      is-torsorial (htpy-section-Dependent-Directed-Graph B f)
    is-torsorial-htpy-section-Dependent-Directed-Graph =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy (vertex-section-Dependent-Directed-Graph B f))
        ( vertex-section-Dependent-Directed-Graph B f , refl-htpy)
        ( is-torsorial-Eq-implicit-Π
          ( λ x →
            is-torsorial-Eq-implicit-Π
              ( λ y →
                is-torsorial-htpy
                  ( edge-section-Dependent-Directed-Graph B f))))

  htpy-eq-section-Dependent-Directed-Graph :
    (g : section-Dependent-Directed-Graph B) →
    f ＝ g → htpy-section-Dependent-Directed-Graph B f g
  htpy-eq-section-Dependent-Directed-Graph g refl =
    refl-htpy-section-Dependent-Directed-Graph B f

  abstract
    is-equiv-htpy-eq-section-Dependent-Directed-Graph :
      (g : section-Dependent-Directed-Graph B) →
      is-equiv (htpy-eq-section-Dependent-Directed-Graph g)
    is-equiv-htpy-eq-section-Dependent-Directed-Graph =
      fundamental-theorem-id
        is-torsorial-htpy-section-Dependent-Directed-Graph
        htpy-eq-section-Dependent-Directed-Graph

  extensionality-section-Dependent-Directed-Graph :
    (g : section-Dependent-Directed-Graph B) →
    (f ＝ g) ≃ htpy-section-Dependent-Directed-Graph B f g
  pr1 (extensionality-section-Dependent-Directed-Graph g) =
    htpy-eq-section-Dependent-Directed-Graph g
  pr2 (extensionality-section-Dependent-Directed-Graph g) =
    is-equiv-htpy-eq-section-Dependent-Directed-Graph g

  eq-htpy-section-Dependent-Directed-Graph :
    (g : section-Dependent-Directed-Graph B) →
    htpy-section-Dependent-Directed-Graph B f g → f ＝ g
  eq-htpy-section-Dependent-Directed-Graph g =
    map-inv-equiv (extensionality-section-Dependent-Directed-Graph g)
```
