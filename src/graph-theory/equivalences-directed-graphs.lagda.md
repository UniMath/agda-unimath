# Equivalences of directed graphs

```agda
module graph-theory.equivalences-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transposition-identifications-along-equivalences
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.morphisms-directed-graphs
```

</details>

## Idea

An
{{#concept "equivalence" Disambiguation="of directed graps" Agda=equiv-Directed-Graph}}
of [directed graphs](graph-theory.directed-graphs.md) from a directed graph
`(V,E)` to a directed graph `(V',E')` consists of an
[equivalence](foundation-core.equivalences.md) `e : V ≃ V'` of vertices, and a
family of equivalences `E x y ≃ E' (e x) (e y)` of edges indexed by `x y : V`.

## Definitions

### Equivalences of directed graphs

```agda
equiv-Directed-Graph :
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
equiv-Directed-Graph G H =
  Σ ( vertex-Directed-Graph G ≃ vertex-Directed-Graph H)
    ( λ e →
      (x y : vertex-Directed-Graph G) →
      edge-Directed-Graph G x y ≃
      edge-Directed-Graph H (map-equiv e x) (map-equiv e y))

module _
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (e : equiv-Directed-Graph G H)
  where

  vertex-equiv-equiv-Directed-Graph :
    vertex-Directed-Graph G ≃ vertex-Directed-Graph H
  vertex-equiv-equiv-Directed-Graph = pr1 e

  vertex-equiv-Directed-Graph :
    vertex-Directed-Graph G → vertex-Directed-Graph H
  vertex-equiv-Directed-Graph = map-equiv vertex-equiv-equiv-Directed-Graph

  is-vertex-equiv-equiv-Directed-Graph :
    is-equiv vertex-equiv-Directed-Graph
  is-vertex-equiv-equiv-Directed-Graph =
    is-equiv-map-equiv vertex-equiv-equiv-Directed-Graph

  inv-vertex-equiv-Directed-Graph :
    vertex-Directed-Graph H → vertex-Directed-Graph G
  inv-vertex-equiv-Directed-Graph =
    map-inv-equiv vertex-equiv-equiv-Directed-Graph

  is-section-inv-vertex-equiv-Directed-Graph :
    ( vertex-equiv-Directed-Graph ∘ inv-vertex-equiv-Directed-Graph) ~ id
  is-section-inv-vertex-equiv-Directed-Graph =
    is-section-map-inv-equiv vertex-equiv-equiv-Directed-Graph

  is-retraction-inv-vertex-equiv-Directed-Graph :
    ( inv-vertex-equiv-Directed-Graph ∘ vertex-equiv-Directed-Graph) ~ id
  is-retraction-inv-vertex-equiv-Directed-Graph =
    is-retraction-map-inv-equiv vertex-equiv-equiv-Directed-Graph

  edge-equiv-equiv-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    edge-Directed-Graph G x y ≃
    edge-Directed-Graph H
      ( vertex-equiv-Directed-Graph x)
      ( vertex-equiv-Directed-Graph y)
  edge-equiv-equiv-Directed-Graph = pr2 e

  edge-equiv-Directed-Graph :
    {x y : vertex-Directed-Graph G} →
    edge-Directed-Graph G x y →
    edge-Directed-Graph H
      ( vertex-equiv-Directed-Graph x)
      ( vertex-equiv-Directed-Graph y)
  edge-equiv-Directed-Graph =
    map-equiv (edge-equiv-equiv-Directed-Graph _ _)

  is-edge-equiv-equiv-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    is-equiv (edge-equiv-Directed-Graph {x} {y})
  is-edge-equiv-equiv-Directed-Graph x y =
    is-equiv-map-equiv (edge-equiv-equiv-Directed-Graph x y)
```

### The condition on a morphism of directed graphs to be an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  where

  is-equiv-hom-Directed-Graph :
    hom-Directed-Graph G H → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-equiv-hom-Directed-Graph f =
    ( is-equiv (vertex-hom-Directed-Graph G H f)) ×
    ( (x y : vertex-Directed-Graph G) →
      is-equiv (edge-hom-Directed-Graph G H f {x} {y}))

  equiv-is-equiv-hom-Directed-Graph :
    (f : hom-Directed-Graph G H) →
    is-equiv-hom-Directed-Graph f → equiv-Directed-Graph G H
  pr1 (equiv-is-equiv-hom-Directed-Graph f (K , L)) =
    ( vertex-hom-Directed-Graph G H f , K)
  pr2 (equiv-is-equiv-hom-Directed-Graph f (K , L)) x y =
    ( edge-hom-Directed-Graph G H f , L x y)

  compute-equiv-Directed-Graph :
    equiv-Directed-Graph G H ≃
    Σ (hom-Directed-Graph G H) is-equiv-hom-Directed-Graph
  compute-equiv-Directed-Graph =
    interchange-Σ-Σ
      ( λ fV H fE → (x y : vertex-Directed-Graph G) → is-equiv (fE x y)) ∘e
      ( equiv-tot
        ( λ fV →
          distributive-Π-Σ ∘e equiv-Π-equiv-family (λ x → distributive-Π-Σ)))

  hom-equiv-Directed-Graph :
    equiv-Directed-Graph G H → hom-Directed-Graph G H
  hom-equiv-Directed-Graph e =
    pr1 (map-equiv compute-equiv-Directed-Graph e)

  compute-hom-equiv-Directed-Graph :
    (e : equiv-Directed-Graph G H) →
    hom-equiv-Directed-Graph e ＝
    ( vertex-equiv-Directed-Graph G H e ,
      λ _ _ → edge-equiv-Directed-Graph G H e)
  compute-hom-equiv-Directed-Graph e = refl

  is-equiv-equiv-Directed-Graph :
    (e : equiv-Directed-Graph G H) →
    is-equiv-hom-Directed-Graph (hom-equiv-Directed-Graph e)
  is-equiv-equiv-Directed-Graph e =
    pr2 (map-equiv compute-equiv-Directed-Graph e)
```

### Identity equivalences of directed graphs

```agda
id-equiv-Directed-Graph :
  {l1 l2 : Level} (G : Directed-Graph l1 l2) → equiv-Directed-Graph G G
pr1 (id-equiv-Directed-Graph G) = id-equiv
pr2 (id-equiv-Directed-Graph G) x y = id-equiv
```

### Composition of equivalences of directed graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (K : Directed-Graph l5 l6)
  (g : equiv-Directed-Graph H K) (f : equiv-Directed-Graph G H)
  where

  vertex-equiv-comp-equiv-Directed-Graph :
    vertex-Directed-Graph G ≃ vertex-Directed-Graph K
  vertex-equiv-comp-equiv-Directed-Graph =
    ( vertex-equiv-equiv-Directed-Graph H K g) ∘e
    ( vertex-equiv-equiv-Directed-Graph G H f)

  vertex-comp-equiv-Directed-Graph :
    vertex-Directed-Graph G → vertex-Directed-Graph K
  vertex-comp-equiv-Directed-Graph =
    map-equiv vertex-equiv-comp-equiv-Directed-Graph

  edge-equiv-comp-equiv-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    edge-Directed-Graph G x y ≃
    edge-Directed-Graph K
      ( vertex-comp-equiv-Directed-Graph x)
      ( vertex-comp-equiv-Directed-Graph y)
  edge-equiv-comp-equiv-Directed-Graph x y =
    ( edge-equiv-equiv-Directed-Graph H K g
      ( vertex-equiv-Directed-Graph G H f x)
      ( vertex-equiv-Directed-Graph G H f y)) ∘e
    ( edge-equiv-equiv-Directed-Graph G H f x y)

  edge-comp-equiv-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    edge-Directed-Graph G x y →
    edge-Directed-Graph K
      ( vertex-comp-equiv-Directed-Graph x)
      ( vertex-comp-equiv-Directed-Graph y)
  edge-comp-equiv-Directed-Graph x y =
    map-equiv (edge-equiv-comp-equiv-Directed-Graph x y)

  comp-equiv-Directed-Graph :
    equiv-Directed-Graph G K
  pr1 comp-equiv-Directed-Graph =
    vertex-equiv-comp-equiv-Directed-Graph
  pr2 comp-equiv-Directed-Graph =
    edge-equiv-comp-equiv-Directed-Graph
```

### Homotopies of equivalences of directed graphs

```agda
htpy-equiv-Directed-Graph :
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (e f : equiv-Directed-Graph G H) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
htpy-equiv-Directed-Graph G H e f =
  htpy-hom-Directed-Graph G H
    ( hom-equiv-Directed-Graph G H e)
    ( hom-equiv-Directed-Graph G H f)
```

### The reflexivity homotopy of equivalences of directed graphs

```agda
refl-htpy-equiv-Directed-Graph :
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (e : equiv-Directed-Graph G H) → htpy-equiv-Directed-Graph G H e e
refl-htpy-equiv-Directed-Graph G H e =
  refl-htpy-hom-Directed-Graph G H (hom-equiv-Directed-Graph G H e)
```

## Properties

### Homotopies characterize identifications of equivalences of directed graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (e : equiv-Directed-Graph G H)
  where

  is-torsorial-htpy-equiv-Directed-Graph :
    is-torsorial (htpy-equiv-Directed-Graph G H e)
  is-torsorial-htpy-equiv-Directed-Graph =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy-equiv (vertex-equiv-equiv-Directed-Graph G H e))
      ( vertex-equiv-equiv-Directed-Graph G H e , refl-htpy)
      ( is-torsorial-Eq-Π
        ( λ x →
          is-torsorial-Eq-Π
            ( λ y →
              is-torsorial-htpy-equiv
                ( edge-equiv-equiv-Directed-Graph G H e x y))))

  htpy-eq-equiv-Directed-Graph :
    (f : equiv-Directed-Graph G H) → e ＝ f → htpy-equiv-Directed-Graph G H e f
  htpy-eq-equiv-Directed-Graph .e refl = refl-htpy-equiv-Directed-Graph G H e

  is-equiv-htpy-eq-equiv-Directed-Graph :
    (f : equiv-Directed-Graph G H) →
    is-equiv (htpy-eq-equiv-Directed-Graph f)
  is-equiv-htpy-eq-equiv-Directed-Graph =
    fundamental-theorem-id
      is-torsorial-htpy-equiv-Directed-Graph
      htpy-eq-equiv-Directed-Graph

  extensionality-equiv-Directed-Graph :
    (f : equiv-Directed-Graph G H) →
    (e ＝ f) ≃ htpy-equiv-Directed-Graph G H e f
  pr1 (extensionality-equiv-Directed-Graph f) = htpy-eq-equiv-Directed-Graph f
  pr2 (extensionality-equiv-Directed-Graph f) =
    is-equiv-htpy-eq-equiv-Directed-Graph f

  eq-htpy-equiv-Directed-Graph :
    (f : equiv-Directed-Graph G H) →
    htpy-equiv-Directed-Graph G H e f → e ＝ f
  eq-htpy-equiv-Directed-Graph f =
    map-inv-equiv (extensionality-equiv-Directed-Graph f)
```

### Equivalences of directed graphs characterize identifications of directed graphs

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  extensionality-Directed-Graph :
    (H : Directed-Graph l1 l2) → (G ＝ H) ≃ equiv-Directed-Graph G H
  extensionality-Directed-Graph =
    extensionality-Σ
      ( λ {V} E e →
        ( x y : vertex-Directed-Graph G) →
        edge-Directed-Graph G x y ≃ E (map-equiv e x) (map-equiv e y))
      ( id-equiv)
      ( λ x y → id-equiv)
      ( λ X → equiv-univalence)
      ( extensionality-Π
          ( λ x y → edge-Directed-Graph G x y)
          ( λ x F →
            (y : vertex-Directed-Graph G) → edge-Directed-Graph G x y ≃ F y)
          ( λ x →
            extensionality-Π
              ( λ y → edge-Directed-Graph G x y)
              ( λ y X → edge-Directed-Graph G x y ≃ X)
              ( λ y X → equiv-univalence)))

  equiv-eq-Directed-Graph :
    (H : Directed-Graph l1 l2) → (G ＝ H) → equiv-Directed-Graph G H
  equiv-eq-Directed-Graph H = map-equiv (extensionality-Directed-Graph H)

  eq-equiv-Directed-Graph :
    (H : Directed-Graph l1 l2) → equiv-Directed-Graph G H → (G ＝ H)
  eq-equiv-Directed-Graph H = map-inv-equiv (extensionality-Directed-Graph H)

  is-torsorial-equiv-Directed-Graph :
    is-torsorial (equiv-Directed-Graph G)
  is-torsorial-equiv-Directed-Graph =
    is-contr-equiv'
      ( Σ (Directed-Graph l1 l2) (λ H → G ＝ H))
      ( equiv-tot extensionality-Directed-Graph)
      ( is-torsorial-Id G)
```

### The inverse of an equivalence of directed trees

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (f : equiv-Directed-Graph G H)
  where

  vertex-equiv-inv-equiv-Directed-Graph :
    vertex-Directed-Graph H ≃ vertex-Directed-Graph G
  vertex-equiv-inv-equiv-Directed-Graph =
    inv-equiv (vertex-equiv-equiv-Directed-Graph G H f)

  vertex-inv-equiv-Directed-Graph :
    vertex-Directed-Graph H → vertex-Directed-Graph G
  vertex-inv-equiv-Directed-Graph =
    map-inv-equiv (vertex-equiv-equiv-Directed-Graph G H f)

  is-section-vertex-inv-equiv-Directed-Graph :
    ( vertex-equiv-Directed-Graph G H f ∘
      vertex-inv-equiv-Directed-Graph) ~ id
  is-section-vertex-inv-equiv-Directed-Graph =
    is-section-map-inv-equiv (vertex-equiv-equiv-Directed-Graph G H f)

  is-retraction-vertex-inv-equiv-Directed-Graph :
    ( vertex-inv-equiv-Directed-Graph ∘
      vertex-equiv-Directed-Graph G H f) ~ id
  is-retraction-vertex-inv-equiv-Directed-Graph =
    is-retraction-map-inv-equiv (vertex-equiv-equiv-Directed-Graph G H f)

  is-vertex-equiv-inv-equiv-Directed-Graph :
    is-equiv vertex-inv-equiv-Directed-Graph
  is-vertex-equiv-inv-equiv-Directed-Graph =
    is-equiv-map-inv-equiv (vertex-equiv-equiv-Directed-Graph G H f)

  edge-equiv-inv-equiv-Directed-Graph :
    (x y : vertex-Directed-Graph H) →
    edge-Directed-Graph H x y ≃
    edge-Directed-Graph G
      ( vertex-inv-equiv-Directed-Graph x)
      ( vertex-inv-equiv-Directed-Graph y)
  edge-equiv-inv-equiv-Directed-Graph x y =
    ( inv-equiv
      ( edge-equiv-equiv-Directed-Graph G H f
        ( vertex-inv-equiv-Directed-Graph x)
        ( vertex-inv-equiv-Directed-Graph y))) ∘e
    ( equiv-binary-tr
      ( edge-Directed-Graph H)
      ( inv (is-section-vertex-inv-equiv-Directed-Graph x))
      ( inv (is-section-vertex-inv-equiv-Directed-Graph y)))

  edge-inv-equiv-Directed-Graph :
    {x y : vertex-Directed-Graph H} →
    edge-Directed-Graph H x y →
    edge-Directed-Graph G
      ( vertex-inv-equiv-Directed-Graph x)
      ( vertex-inv-equiv-Directed-Graph y)
  edge-inv-equiv-Directed-Graph =
    map-equiv (edge-equiv-inv-equiv-Directed-Graph _ _)

  hom-inv-equiv-Directed-Graph : hom-Directed-Graph H G
  pr1 hom-inv-equiv-Directed-Graph = vertex-inv-equiv-Directed-Graph
  pr2 hom-inv-equiv-Directed-Graph _ _ = edge-inv-equiv-Directed-Graph

  inv-equiv-Directed-Graph : equiv-Directed-Graph H G
  pr1 inv-equiv-Directed-Graph = vertex-equiv-inv-equiv-Directed-Graph
  pr2 inv-equiv-Directed-Graph = edge-equiv-inv-equiv-Directed-Graph

  vertex-is-section-inv-equiv-Directed-Graph :
    ( vertex-equiv-Directed-Graph G H f ∘ vertex-inv-equiv-Directed-Graph) ~ id
  vertex-is-section-inv-equiv-Directed-Graph =
    is-section-vertex-inv-equiv-Directed-Graph

  edge-is-section-inv-equiv-Directed-Graph :
    (x y : vertex-Directed-Graph H) (e : edge-Directed-Graph H x y) →
    binary-tr
      ( edge-Directed-Graph H)
      ( vertex-is-section-inv-equiv-Directed-Graph x)
      ( vertex-is-section-inv-equiv-Directed-Graph y)
      ( edge-equiv-Directed-Graph G H f
        ( edge-inv-equiv-Directed-Graph e)) ＝ e
  edge-is-section-inv-equiv-Directed-Graph x y e =
    ( ap
      ( binary-tr
        ( edge-Directed-Graph H)
        ( vertex-is-section-inv-equiv-Directed-Graph x)
        ( vertex-is-section-inv-equiv-Directed-Graph y))
        ( is-section-map-inv-equiv
          ( edge-equiv-equiv-Directed-Graph G H f
            ( vertex-inv-equiv-Directed-Graph x)
            ( vertex-inv-equiv-Directed-Graph y))
          ( binary-tr
            ( edge-Directed-Graph H)
            ( inv (is-section-map-inv-equiv (pr1 f) x))
            ( inv (is-section-map-inv-equiv (pr1 f) y))
            ( e)))) ∙
    ( ( inv
        ( binary-tr-concat
          ( edge-Directed-Graph H)
          ( inv (vertex-is-section-inv-equiv-Directed-Graph x))
          ( vertex-is-section-inv-equiv-Directed-Graph x)
          ( inv (vertex-is-section-inv-equiv-Directed-Graph y))
          ( vertex-is-section-inv-equiv-Directed-Graph y)
          ( e))) ∙
      ( ap-binary
        ( λ p q → binary-tr (edge-Directed-Graph H) p q e)
        ( left-inv (vertex-is-section-inv-equiv-Directed-Graph x))
        ( left-inv (vertex-is-section-inv-equiv-Directed-Graph y))))

  is-section-inv-equiv-Directed-Graph :
    htpy-equiv-Directed-Graph H H
      ( comp-equiv-Directed-Graph H G H f (inv-equiv-Directed-Graph))
      ( id-equiv-Directed-Graph H)
  pr1 is-section-inv-equiv-Directed-Graph =
    vertex-is-section-inv-equiv-Directed-Graph
  pr2 is-section-inv-equiv-Directed-Graph =
    edge-is-section-inv-equiv-Directed-Graph

  vertex-is-retraction-inv-equiv-Directed-Graph :
    ( vertex-inv-equiv-Directed-Graph ∘ vertex-equiv-Directed-Graph G H f) ~ id
  vertex-is-retraction-inv-equiv-Directed-Graph =
    is-retraction-vertex-inv-equiv-Directed-Graph

  edge-is-retraction-inv-equiv-Directed-Graph :
    (x y : vertex-Directed-Graph G) (e : edge-Directed-Graph G x y) →
    binary-tr
      ( edge-Directed-Graph G)
      ( vertex-is-retraction-inv-equiv-Directed-Graph x)
      ( vertex-is-retraction-inv-equiv-Directed-Graph y)
      ( edge-inv-equiv-Directed-Graph (edge-equiv-Directed-Graph G H f e)) ＝ e
  edge-is-retraction-inv-equiv-Directed-Graph x y e =
    transpose-binary-path-over'
      ( edge-Directed-Graph G)
      ( vertex-is-retraction-inv-equiv-Directed-Graph x)
      ( vertex-is-retraction-inv-equiv-Directed-Graph y)
      ( map-eq-transpose-equiv-inv
        ( edge-equiv-equiv-Directed-Graph G H f
          ( vertex-inv-equiv-Directed-Graph
            ( vertex-equiv-Directed-Graph G H f x))
          ( vertex-inv-equiv-Directed-Graph
            ( vertex-equiv-Directed-Graph G H f y)))
        ( ( ap-binary
            ( λ u v →
              binary-tr
                ( edge-Directed-Graph H)
                ( u)
                ( v)
                ( edge-equiv-Directed-Graph G H f e))
            ( ( ap
                ( inv)
                ( coherence-map-inv-equiv
                  ( vertex-equiv-equiv-Directed-Graph G H f)
                  ( x))) ∙
              ( inv
                ( ap-inv
                  ( vertex-equiv-Directed-Graph G H f)
                  ( vertex-is-retraction-inv-equiv-Directed-Graph x))))
            ( ( ap
                ( inv)
                ( coherence-map-inv-equiv
                  ( vertex-equiv-equiv-Directed-Graph G H f)
                  ( y))) ∙
              ( inv
                ( ap-inv
                  ( vertex-equiv-Directed-Graph G H f)
                  ( vertex-is-retraction-inv-equiv-Directed-Graph y))))) ∙
          ( binary-tr-ap
            ( edge-Directed-Graph H)
            ( λ _ _ → edge-equiv-Directed-Graph G H f)
            ( inv (vertex-is-retraction-inv-equiv-Directed-Graph x))
            ( inv (vertex-is-retraction-inv-equiv-Directed-Graph y))
            ( refl))))

  is-retraction-inv-equiv-Directed-Graph :
    htpy-equiv-Directed-Graph G G
      ( comp-equiv-Directed-Graph G H G (inv-equiv-Directed-Graph) f)
      ( id-equiv-Directed-Graph G)
  pr1 is-retraction-inv-equiv-Directed-Graph =
    vertex-is-retraction-inv-equiv-Directed-Graph
  pr2 is-retraction-inv-equiv-Directed-Graph =
    edge-is-retraction-inv-equiv-Directed-Graph
```

## External links

- [Graph isomoprhism](https://www.wikidata.org/entity/Q303100) at Wikidata
- [Graph isomorphism](https://en.wikipedia.org/wiki/Graph_isomorphism) at
  Wikipedia
- [Graph isomorphism](https://mathworld.wolfram.com/GraphIsomorphism.html) at
  Wolfram MathWorld
- [Isomorphism](https://ncatlab.org/nlab/show/isomorphism) at $n$Lab
