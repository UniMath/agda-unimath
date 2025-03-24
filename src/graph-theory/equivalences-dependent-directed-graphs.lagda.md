# Equivalences of dependent directed graphs

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module graph-theory.equivalences-dependent-directed-graphs
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types funext
open import foundation.equivalences funext
open import foundation.families-of-equivalences funext
open import foundation.function-types funext
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types funext
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families funext univalence truncations
open import foundation.univalence funext univalence
open import foundation.universe-levels

open import graph-theory.dependent-directed-graphs funext univalence
open import graph-theory.directed-graphs funext univalence
```

</details>

## Idea

Consider two
[dependent directed graphs](graph-theory.dependent-directed-graphs.md) `H` and
`K` over a [directed graph](graph-theory.directed-graphs.md) `G`. An
{{#concept "equivalence of dependent directed graphs" Agda=equiv-Dependent-Directed-Graph}}
from `H` to `K` consists of a
[family of equivalences](foundation.families-of-equivalences.md)

```text
  e₀ : {x : G₀} → H₀ x ≃ K₀ x
```

of vertices, and a family of [equivalences](foundation-core.equivalences.md)

```text
  e₁ : {x y : G₀} (a : G₁ x y) {y : H₀ x} {y' : H₀ x'} → H₁ a y y' ≃ K₁ a (e₀ y) (e₀ y')
```

of edges.

## Definitions

### Equivalences of dependent directed graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} {G : Directed-Graph l1 l2}
  (H : Dependent-Directed-Graph l3 l4 G)
  (K : Dependent-Directed-Graph l5 l6 G)
  where

  equiv-Dependent-Directed-Graph : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  equiv-Dependent-Directed-Graph =
    Σ ( fam-equiv
        ( vertex-Dependent-Directed-Graph H)
        ( vertex-Dependent-Directed-Graph K))
      ( λ e →
        (x x' : vertex-Directed-Graph G) →
        (a : edge-Directed-Graph G x x') →
        (y : vertex-Dependent-Directed-Graph H x)
        (y' : vertex-Dependent-Directed-Graph H x') →
        edge-Dependent-Directed-Graph H a y y' ≃
        edge-Dependent-Directed-Graph K a
          ( map-equiv (e x) y)
          ( map-equiv (e x') y'))

  vertex-equiv-equiv-Dependent-Directed-Graph :
    equiv-Dependent-Directed-Graph →
    fam-equiv
      ( vertex-Dependent-Directed-Graph H)
      ( vertex-Dependent-Directed-Graph K)
  vertex-equiv-equiv-Dependent-Directed-Graph = pr1

  vertex-equiv-Dependent-Directed-Graph :
    equiv-Dependent-Directed-Graph →
    {x : vertex-Directed-Graph G} →
    vertex-Dependent-Directed-Graph H x →
    vertex-Dependent-Directed-Graph K x
  vertex-equiv-Dependent-Directed-Graph e {x} =
    map-equiv (vertex-equiv-equiv-Dependent-Directed-Graph e x)

  edge-equiv-equiv-Dependent-Directed-Graph :
    (e : equiv-Dependent-Directed-Graph) →
    {x x' : vertex-Directed-Graph G}
    (a : edge-Directed-Graph G x x')
    (y : vertex-Dependent-Directed-Graph H x)
    (y' : vertex-Dependent-Directed-Graph H x') →
    edge-Dependent-Directed-Graph H a y y' ≃
    edge-Dependent-Directed-Graph K a
      ( vertex-equiv-Dependent-Directed-Graph e y)
      ( vertex-equiv-Dependent-Directed-Graph e y')
  edge-equiv-equiv-Dependent-Directed-Graph e a =
    pr2 e _ _ a

  edge-equiv-Dependent-Directed-Graph :
    (e : equiv-Dependent-Directed-Graph) →
    {x x' : vertex-Directed-Graph G}
    {a : edge-Directed-Graph G x x'}
    {y : vertex-Dependent-Directed-Graph H x}
    {y' : vertex-Dependent-Directed-Graph H x'} →
    edge-Dependent-Directed-Graph H a y y' →
    edge-Dependent-Directed-Graph K a
      ( vertex-equiv-Dependent-Directed-Graph e y)
      ( vertex-equiv-Dependent-Directed-Graph e y')
  edge-equiv-Dependent-Directed-Graph e =
    map-equiv (edge-equiv-equiv-Dependent-Directed-Graph e _ _ _)
```

### The identity equivalence of a dependent directed graph

```agda
module _
  {l1 l2 l3 l4 : Level} {G : Directed-Graph l1 l2}
  (H : Dependent-Directed-Graph l3 l4 G)
  where

  vertex-equiv-id-equiv-Dependent-Directed-Graph :
    fam-equiv
      ( vertex-Dependent-Directed-Graph H)
      ( vertex-Dependent-Directed-Graph H)
  vertex-equiv-id-equiv-Dependent-Directed-Graph x = id-equiv

  vertex-id-equiv-Dependent-Directed-Graph :
    {x : vertex-Directed-Graph G} →
    vertex-Dependent-Directed-Graph H x →
    vertex-Dependent-Directed-Graph H x
  vertex-id-equiv-Dependent-Directed-Graph = id

  edge-equiv-id-equiv-Dependent-Directed-Graph :
    {x x' : vertex-Directed-Graph G}
    (a : edge-Directed-Graph G x x')
    (y : vertex-Dependent-Directed-Graph H x)
    (y' : vertex-Dependent-Directed-Graph H x') →
    edge-Dependent-Directed-Graph H a y y' ≃
    edge-Dependent-Directed-Graph H a
      ( vertex-id-equiv-Dependent-Directed-Graph y)
      ( vertex-id-equiv-Dependent-Directed-Graph y')
  edge-equiv-id-equiv-Dependent-Directed-Graph a y y' = id-equiv

  id-equiv-Dependent-Directed-Graph :
    equiv-Dependent-Directed-Graph H H
  pr1 id-equiv-Dependent-Directed-Graph =
    vertex-equiv-id-equiv-Dependent-Directed-Graph
  pr2 id-equiv-Dependent-Directed-Graph _ _ =
    edge-equiv-id-equiv-Dependent-Directed-Graph
```

## Properties

### Equivalences characterize identifications of dependent directed graphs

```agda
module _
  {l1 l2 l3 l4 : Level} {G : Directed-Graph l1 l2}
  (H : Dependent-Directed-Graph l3 l4 G)
  where

  abstract
    is-torsorial-equiv-Dependent-Directed-Graph :
      is-torsorial (equiv-Dependent-Directed-Graph {l5 = l3} {l6 = l4} H)
    is-torsorial-equiv-Dependent-Directed-Graph =
      is-torsorial-Eq-structure
        ( is-torsorial-equiv-fam (vertex-Dependent-Directed-Graph H))
        ( vertex-Dependent-Directed-Graph H , id-equiv-fam _)
        ( is-torsorial-Eq-Π
          ( λ x →
            is-torsorial-Eq-Π
              ( λ x' →
                is-torsorial-Eq-Π
                  ( λ a →
                    is-torsorial-Eq-Π
                      ( λ y →
                        is-torsorial-Eq-Π
                          ( λ y' → is-torsorial-equiv _))))))

  equiv-eq-Dependent-Directed-Graph :
    (K : Dependent-Directed-Graph l3 l4 G) →
    H ＝ K → equiv-Dependent-Directed-Graph H K
  equiv-eq-Dependent-Directed-Graph K refl =
    id-equiv-Dependent-Directed-Graph H

  abstract
    is-equiv-equiv-eq-Dependent-Directed-Graph :
      (K : Dependent-Directed-Graph l3 l4 G) →
      is-equiv (equiv-eq-Dependent-Directed-Graph K)
    is-equiv-equiv-eq-Dependent-Directed-Graph =
      fundamental-theorem-id
        is-torsorial-equiv-Dependent-Directed-Graph
        equiv-eq-Dependent-Directed-Graph

  extensionality-Dependent-Directed-Graph :
    (K : Dependent-Directed-Graph l3 l4 G) →
    (H ＝ K) ≃ equiv-Dependent-Directed-Graph H K
  pr1 (extensionality-Dependent-Directed-Graph K) =
    equiv-eq-Dependent-Directed-Graph K
  pr2 (extensionality-Dependent-Directed-Graph K) =
    is-equiv-equiv-eq-Dependent-Directed-Graph K

  eq-equiv-Dependent-Directed-Graph :
    (K : Dependent-Directed-Graph l3 l4 G) →
    equiv-Dependent-Directed-Graph H K → H ＝ K
  eq-equiv-Dependent-Directed-Graph K =
    map-inv-equiv (extensionality-Dependent-Directed-Graph K)
```
