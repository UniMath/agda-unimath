# Morphisms of directed graphs

```agda
module graph-theory.morphisms-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-dependent-identifications
open import foundation.binary-transport
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

open import graph-theory.directed-graphs
```

</details>

## Idea

A
{{#concept "morphism" Disambiguation="of directed graphs" WD="graph homomorphism" WDID=Q3385162 Agda=hom-Directed-Graph}}
of [directed graphs](graph-theory.directed-graphs.md) from `G` to `H` consists
of a map `f` from the vertices of `G` to the vertices of `H`, and a family of
maps from the edges `E_G x y` in `G` to the edges `E_H (f x) (f y)` in `H`.

## Definitions

### Morphisms of directed graphs

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  where

  hom-Directed-Graph : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Directed-Graph =
    Σ ( vertex-Directed-Graph G → vertex-Directed-Graph H)
      ( λ α →
        (x y : vertex-Directed-Graph G) →
        edge-Directed-Graph G x y → edge-Directed-Graph H (α x) (α y))

  module _
    (f : hom-Directed-Graph)
    where

    vertex-hom-Directed-Graph :
      vertex-Directed-Graph G → vertex-Directed-Graph H
    vertex-hom-Directed-Graph = pr1 f

    edge-hom-Directed-Graph :
      {x y : vertex-Directed-Graph G} (e : edge-Directed-Graph G x y) →
      edge-Directed-Graph H
        ( vertex-hom-Directed-Graph x)
        ( vertex-hom-Directed-Graph y)
    edge-hom-Directed-Graph {x} {y} e = pr2 f x y e

    direct-predecessor-hom-Directed-Graph :
      (x : vertex-Directed-Graph G) →
      direct-predecessor-Directed-Graph G x →
      direct-predecessor-Directed-Graph H (vertex-hom-Directed-Graph x)
    direct-predecessor-hom-Directed-Graph x =
      map-Σ
        ( λ y → edge-Directed-Graph H y (vertex-hom-Directed-Graph x))
        ( vertex-hom-Directed-Graph)
        ( λ y → edge-hom-Directed-Graph)

    direct-successor-hom-Directed-Graph :
      (x : vertex-Directed-Graph G) →
      direct-successor-Directed-Graph G x →
      direct-successor-Directed-Graph H (vertex-hom-Directed-Graph x)
    direct-successor-hom-Directed-Graph x =
      map-Σ
        ( edge-Directed-Graph H (vertex-hom-Directed-Graph x))
        ( vertex-hom-Directed-Graph)
        ( λ y → edge-hom-Directed-Graph)
```

### Composition of morphisms of directed graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (K : Directed-Graph l5 l6)
  where

  vertex-comp-hom-Directed-Graph :
    hom-Directed-Graph H K → hom-Directed-Graph G H →
    vertex-Directed-Graph G → vertex-Directed-Graph K
  vertex-comp-hom-Directed-Graph g f =
    (vertex-hom-Directed-Graph H K g) ∘ (vertex-hom-Directed-Graph G H f)

  edge-comp-hom-Directed-Graph :
    (g : hom-Directed-Graph H K) (f : hom-Directed-Graph G H)
    (x y : vertex-Directed-Graph G) →
    edge-Directed-Graph G x y →
    edge-Directed-Graph K
      ( vertex-comp-hom-Directed-Graph g f x)
      ( vertex-comp-hom-Directed-Graph g f y)
  edge-comp-hom-Directed-Graph g f x y e =
    edge-hom-Directed-Graph H K g (edge-hom-Directed-Graph G H f e)

  comp-hom-Directed-Graph :
    hom-Directed-Graph H K → hom-Directed-Graph G H →
    hom-Directed-Graph G K
  pr1 (comp-hom-Directed-Graph g f) = vertex-comp-hom-Directed-Graph g f
  pr2 (comp-hom-Directed-Graph g f) = edge-comp-hom-Directed-Graph g f
```

### Identity morphisms of directed graphs

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  id-hom-Directed-Graph : hom-Directed-Graph G G
  pr1 id-hom-Directed-Graph = id
  pr2 id-hom-Directed-Graph _ _ = id
```

## Properties

### Characterizing the identity type of morphisms graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  where

  htpy-hom-Directed-Graph :
    (f g : hom-Directed-Graph G H) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-Directed-Graph f g =
    Σ ( vertex-hom-Directed-Graph G H f ~ vertex-hom-Directed-Graph G H g)
      ( λ α →
        ( x y : vertex-Directed-Graph G) (e : edge-Directed-Graph G x y) →
        binary-dependent-identification
          ( edge-Directed-Graph H)
          ( α x)
          ( α y)
          ( edge-hom-Directed-Graph G H f e)
          ( edge-hom-Directed-Graph G H g e))

  module _
    (f g : hom-Directed-Graph G H) (α : htpy-hom-Directed-Graph f g)
    where

    vertex-htpy-hom-Directed-Graph :
      vertex-hom-Directed-Graph G H f ~ vertex-hom-Directed-Graph G H g
    vertex-htpy-hom-Directed-Graph = pr1 α

    edge-htpy-hom-Directed-Graph :
      (x y : vertex-Directed-Graph G) (e : edge-Directed-Graph G x y) →
      binary-dependent-identification
        ( edge-Directed-Graph H)
        ( vertex-htpy-hom-Directed-Graph x)
        ( vertex-htpy-hom-Directed-Graph y)
        ( edge-hom-Directed-Graph G H f e)
        ( edge-hom-Directed-Graph G H g e)
    edge-htpy-hom-Directed-Graph = pr2 α

  refl-htpy-hom-Directed-Graph :
    (f : hom-Directed-Graph G H) → htpy-hom-Directed-Graph f f
  pr1 (refl-htpy-hom-Directed-Graph f) = refl-htpy
  pr2 (refl-htpy-hom-Directed-Graph f) x y e = refl

  htpy-eq-hom-Directed-Graph :
    (f g : hom-Directed-Graph G H) → f ＝ g → htpy-hom-Directed-Graph f g
  htpy-eq-hom-Directed-Graph f .f refl = refl-htpy-hom-Directed-Graph f

  is-torsorial-htpy-hom-Directed-Graph :
    (f : hom-Directed-Graph G H) →
    is-torsorial (htpy-hom-Directed-Graph f)
  is-torsorial-htpy-hom-Directed-Graph f =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (vertex-hom-Directed-Graph G H f))
      ( pair
        ( vertex-hom-Directed-Graph G H f)
        ( refl-htpy))
      ( is-torsorial-Eq-Π
        ( λ x →
          is-torsorial-Eq-Π
            ( λ y → is-torsorial-htpy (edge-hom-Directed-Graph G H f))))

  is-equiv-htpy-eq-hom-Directed-Graph :
    (f g : hom-Directed-Graph G H) → is-equiv (htpy-eq-hom-Directed-Graph f g)
  is-equiv-htpy-eq-hom-Directed-Graph f =
    fundamental-theorem-id
      ( is-torsorial-htpy-hom-Directed-Graph f)
      ( htpy-eq-hom-Directed-Graph f)

  extensionality-hom-Directed-Graph :
    (f g : hom-Directed-Graph G H) → (f ＝ g) ≃ htpy-hom-Directed-Graph f g
  pr1 (extensionality-hom-Directed-Graph f g) = htpy-eq-hom-Directed-Graph f g
  pr2 (extensionality-hom-Directed-Graph f g) =
    is-equiv-htpy-eq-hom-Directed-Graph f g

  eq-htpy-hom-Directed-Graph :
    (f g : hom-Directed-Graph G H) → htpy-hom-Directed-Graph f g → (f ＝ g)
  eq-htpy-hom-Directed-Graph f g =
    map-inv-equiv (extensionality-hom-Directed-Graph f g)
```

### The left unit law of composition of morphisms of directed graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (f : hom-Directed-Graph G H)
  where

  vertex-left-unit-law-comp-hom-Directed-Graph :
    vertex-comp-hom-Directed-Graph G H H (id-hom-Directed-Graph H) f ~
    vertex-hom-Directed-Graph G H f
  vertex-left-unit-law-comp-hom-Directed-Graph = refl-htpy

  edge-left-unit-law-comp-hom-Directed-Graph :
    {x y : vertex-Directed-Graph G} →
    edge-comp-hom-Directed-Graph G H H (id-hom-Directed-Graph H) f x y ~
    edge-hom-Directed-Graph G H f
  edge-left-unit-law-comp-hom-Directed-Graph = refl-htpy

  left-unit-law-comp-hom-Directed-Graph :
    htpy-hom-Directed-Graph G H
      ( comp-hom-Directed-Graph G H H (id-hom-Directed-Graph H) f)
      ( f)
  pr1 left-unit-law-comp-hom-Directed-Graph =
    vertex-left-unit-law-comp-hom-Directed-Graph
  pr2 left-unit-law-comp-hom-Directed-Graph _ _ =
    edge-left-unit-law-comp-hom-Directed-Graph
```

### The right unit law of composition of morphisms of directed graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (f : hom-Directed-Graph G H)
  where

  vertex-right-unit-law-comp-hom-Directed-Graph :
    vertex-comp-hom-Directed-Graph G G H f (id-hom-Directed-Graph G) ~
    vertex-hom-Directed-Graph G H f
  vertex-right-unit-law-comp-hom-Directed-Graph = refl-htpy

  edge-right-unit-law-comp-hom-Directed-Graph :
    {x y : vertex-Directed-Graph G} →
    edge-comp-hom-Directed-Graph G G H f (id-hom-Directed-Graph G) x y ~
    edge-hom-Directed-Graph G H f
  edge-right-unit-law-comp-hom-Directed-Graph = refl-htpy

  right-unit-law-comp-hom-Directed-Graph :
    htpy-hom-Directed-Graph G H
      ( comp-hom-Directed-Graph G G H f (id-hom-Directed-Graph G))
      ( f)
  pr1 right-unit-law-comp-hom-Directed-Graph =
    vertex-right-unit-law-comp-hom-Directed-Graph
  pr2 right-unit-law-comp-hom-Directed-Graph _ _ =
    edge-right-unit-law-comp-hom-Directed-Graph
```

### Associativity of composition of morphisms of directed graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (K : Directed-Graph l5 l6) (L : Directed-Graph l7 l8)
  (h : hom-Directed-Graph K L)
  (g : hom-Directed-Graph H K)
  (f : hom-Directed-Graph G H)
  where

  associative-comp-hom-Directed-Graph :
    htpy-hom-Directed-Graph G L
      ( comp-hom-Directed-Graph G H L (comp-hom-Directed-Graph H K L h g) f)
      ( comp-hom-Directed-Graph G K L h (comp-hom-Directed-Graph G H K g f))
  associative-comp-hom-Directed-Graph =
    refl-htpy-hom-Directed-Graph G L _
```

## External links

- [Graph homomorphism](https://www.wikidata.org/entity/Q3385162) on Wikidata
- [Graph homomorphism](https://en.wikipedia.org/wiki/Graph_homomorphism) at
  Wikipedia
