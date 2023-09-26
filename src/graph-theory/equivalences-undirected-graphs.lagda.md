# Equivalences of undirected graphs

```agda
module graph-theory.equivalences-undirected-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
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
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.morphisms-undirected-graphs
open import graph-theory.undirected-graphs
```

</details>

## Idea

An equivalence of undirected graphs is a morphism of undirected graphs that
induces an equivalence on vertices and equivalences on edges.

## Definitions

### Equivalences of undirected graphs

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  where

  equiv-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-Undirected-Graph =
    Σ ( vertex-Undirected-Graph G ≃ vertex-Undirected-Graph H)
      ( λ f →
        ( p : unordered-pair-vertices-Undirected-Graph G) →
        edge-Undirected-Graph G p ≃
        edge-Undirected-Graph H (map-equiv-unordered-pair f p))

  equiv-vertex-equiv-Undirected-Graph :
    equiv-Undirected-Graph →
    vertex-Undirected-Graph G ≃ vertex-Undirected-Graph H
  equiv-vertex-equiv-Undirected-Graph f = pr1 f

  vertex-equiv-Undirected-Graph :
    equiv-Undirected-Graph →
    vertex-Undirected-Graph G → vertex-Undirected-Graph H
  vertex-equiv-Undirected-Graph f =
    map-equiv (equiv-vertex-equiv-Undirected-Graph f)

  equiv-unordered-pair-vertices-equiv-Undirected-Graph :
    equiv-Undirected-Graph →
    unordered-pair-vertices-Undirected-Graph G ≃
    unordered-pair-vertices-Undirected-Graph H
  equiv-unordered-pair-vertices-equiv-Undirected-Graph f =
    equiv-unordered-pair (equiv-vertex-equiv-Undirected-Graph f)

  unordered-pair-vertices-equiv-Undirected-Graph :
    equiv-Undirected-Graph →
    unordered-pair-vertices-Undirected-Graph G →
    unordered-pair-vertices-Undirected-Graph H
  unordered-pair-vertices-equiv-Undirected-Graph f =
    map-equiv-unordered-pair (equiv-vertex-equiv-Undirected-Graph f)

  standard-unordered-pair-vertices-equiv-Undirected-Graph :
    (e : equiv-Undirected-Graph) (x y : vertex-Undirected-Graph G) →
    unordered-pair-vertices-equiv-Undirected-Graph
      ( e)
      ( standard-unordered-pair x y) ＝
    standard-unordered-pair
      ( vertex-equiv-Undirected-Graph e x)
      ( vertex-equiv-Undirected-Graph e y)
  standard-unordered-pair-vertices-equiv-Undirected-Graph e =
    equiv-standard-unordered-pair (equiv-vertex-equiv-Undirected-Graph e)

  equiv-edge-equiv-Undirected-Graph :
    (f : equiv-Undirected-Graph)
    (p : unordered-pair-vertices-Undirected-Graph G) →
    edge-Undirected-Graph G p ≃
    edge-Undirected-Graph H
      ( unordered-pair-vertices-equiv-Undirected-Graph f p)
  equiv-edge-equiv-Undirected-Graph f = pr2 f

  edge-equiv-Undirected-Graph :
    (f : equiv-Undirected-Graph)
    (p : unordered-pair-vertices-Undirected-Graph G) →
    edge-Undirected-Graph G p →
    edge-Undirected-Graph H
      ( unordered-pair-vertices-equiv-Undirected-Graph f p)
  edge-equiv-Undirected-Graph f p =
    map-equiv (equiv-edge-equiv-Undirected-Graph f p)

  equiv-edge-standard-unordered-pair-vertices-equiv-Undirected-Graph :
    (e : equiv-Undirected-Graph) (x y : vertex-Undirected-Graph G) →
    edge-Undirected-Graph G (standard-unordered-pair x y) ≃
    edge-Undirected-Graph H
      ( standard-unordered-pair
        ( vertex-equiv-Undirected-Graph e x)
        ( vertex-equiv-Undirected-Graph e y))
  equiv-edge-standard-unordered-pair-vertices-equiv-Undirected-Graph e x y =
    ( equiv-tr
      ( edge-Undirected-Graph H)
      ( standard-unordered-pair-vertices-equiv-Undirected-Graph e x y)) ∘e
    ( equiv-edge-equiv-Undirected-Graph e (standard-unordered-pair x y))

  edge-standard-unordered-pair-vertices-equiv-Undirected-Graph :
    (e : equiv-Undirected-Graph) (x y : vertex-Undirected-Graph G) →
    edge-Undirected-Graph G (standard-unordered-pair x y) →
    edge-Undirected-Graph H
      ( standard-unordered-pair
        ( vertex-equiv-Undirected-Graph e x)
        ( vertex-equiv-Undirected-Graph e y))
  edge-standard-unordered-pair-vertices-equiv-Undirected-Graph e x y =
    map-equiv
      ( equiv-edge-standard-unordered-pair-vertices-equiv-Undirected-Graph
          e x y)

  hom-equiv-Undirected-Graph :
    equiv-Undirected-Graph → hom-Undirected-Graph G H
  pr1 (hom-equiv-Undirected-Graph f) = vertex-equiv-Undirected-Graph f
  pr2 (hom-equiv-Undirected-Graph f) = edge-equiv-Undirected-Graph f
```

### The identity equivalence of unordered graphs

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  id-equiv-Undirected-Graph : equiv-Undirected-Graph G G
  pr1 id-equiv-Undirected-Graph = id-equiv
  pr2 id-equiv-Undirected-Graph p = id-equiv

  edge-standard-unordered-pair-vertices-id-equiv-Undirected-Graph :
    (x y : vertex-Undirected-Graph G) →
    ( edge-standard-unordered-pair-vertices-equiv-Undirected-Graph G G
      ( id-equiv-Undirected-Graph) x y) ~
    ( id)
  edge-standard-unordered-pair-vertices-id-equiv-Undirected-Graph x y e =
    ap
      ( λ t → tr (edge-Undirected-Graph G) t e)
      ( id-equiv-standard-unordered-pair x y)
```

## Properties

### Characterizing the identity type of equivalences of unordered graphs

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  where

  htpy-equiv-Undirected-Graph :
    (f g : equiv-Undirected-Graph G H) → UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-equiv-Undirected-Graph f g =
    htpy-hom-Undirected-Graph G H
      ( hom-equiv-Undirected-Graph G H f)
      ( hom-equiv-Undirected-Graph G H g)

  refl-htpy-equiv-Undirected-Graph :
    (f : equiv-Undirected-Graph G H) → htpy-equiv-Undirected-Graph f f
  refl-htpy-equiv-Undirected-Graph f =
    refl-htpy-hom-Undirected-Graph G H (hom-equiv-Undirected-Graph G H f)

  htpy-eq-equiv-Undirected-Graph :
    (f g : equiv-Undirected-Graph G H) → Id f g →
    htpy-equiv-Undirected-Graph f g
  htpy-eq-equiv-Undirected-Graph f .f refl = refl-htpy-equiv-Undirected-Graph f

  is-contr-total-htpy-equiv-Undirected-Graph :
    (f : equiv-Undirected-Graph G H) →
    is-contr (Σ (equiv-Undirected-Graph G H) (htpy-equiv-Undirected-Graph f))
  is-contr-total-htpy-equiv-Undirected-Graph f =
    is-contr-total-Eq-structure
      ( λ gV gE α →
        ( p : unordered-pair-vertices-Undirected-Graph G) →
          ( e : edge-Undirected-Graph G p) →
          Id
            ( tr
              ( edge-Undirected-Graph H)
              ( htpy-unordered-pair α p)
              ( edge-equiv-Undirected-Graph G H f p e))
            ( map-equiv (gE p) e))
      ( is-contr-total-htpy-equiv (equiv-vertex-equiv-Undirected-Graph G H f))
      ( pair (equiv-vertex-equiv-Undirected-Graph G H f) refl-htpy)
      ( is-contr-equiv'
        ( Σ ( (p : unordered-pair-vertices-Undirected-Graph G) →
              edge-Undirected-Graph G p ≃
              edge-Undirected-Graph H
                ( unordered-pair-vertices-equiv-Undirected-Graph G H f p))
            ( λ gE →
              (p : unordered-pair-vertices-Undirected-Graph G) →
              (e : edge-Undirected-Graph G p) →
              Id (edge-equiv-Undirected-Graph G H f p e) (map-equiv (gE p) e)))
        ( equiv-tot
          ( λ gE →
            equiv-Π-equiv-family
              ( λ p →
                equiv-Π-equiv-family
                  ( λ e →
                    equiv-concat
                      ( pr2 (refl-htpy-equiv-Undirected-Graph f) p e)
                      ( map-equiv (gE p) e)))))
        ( is-contr-total-Eq-Π
          ( λ p e →
            htpy-equiv
              ( equiv-edge-equiv-Undirected-Graph G H f p)
              ( e))
          ( λ p →
            is-contr-total-htpy-equiv
              ( equiv-edge-equiv-Undirected-Graph G H f p))))

  is-equiv-htpy-eq-equiv-Undirected-Graph :
    (f g : equiv-Undirected-Graph G H) →
    is-equiv (htpy-eq-equiv-Undirected-Graph f g)
  is-equiv-htpy-eq-equiv-Undirected-Graph f =
    fundamental-theorem-id
      ( is-contr-total-htpy-equiv-Undirected-Graph f)
      ( htpy-eq-equiv-Undirected-Graph f)

  extensionality-equiv-Undirected-Graph :
    (f g : equiv-Undirected-Graph G H) →
    Id f g ≃ htpy-equiv-Undirected-Graph f g
  pr1 (extensionality-equiv-Undirected-Graph f g) =
    htpy-eq-equiv-Undirected-Graph f g
  pr2 (extensionality-equiv-Undirected-Graph f g) =
    is-equiv-htpy-eq-equiv-Undirected-Graph f g

  eq-htpy-equiv-Undirected-Graph :
    (f g : equiv-Undirected-Graph G H) →
    htpy-equiv-Undirected-Graph f g → Id f g
  eq-htpy-equiv-Undirected-Graph f g =
    map-inv-is-equiv (is-equiv-htpy-eq-equiv-Undirected-Graph f g)
```

### Univalence for unordered graphs

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  equiv-eq-Undirected-Graph :
    (H : Undirected-Graph l1 l2) → Id G H → equiv-Undirected-Graph G H
  equiv-eq-Undirected-Graph .G refl = id-equiv-Undirected-Graph G

  is-contr-total-equiv-Undirected-Graph :
    is-contr (Σ (Undirected-Graph l1 l2) (equiv-Undirected-Graph G))
  is-contr-total-equiv-Undirected-Graph =
    is-contr-total-Eq-structure
      ( λ VH VE e →
        ( p : unordered-pair-vertices-Undirected-Graph G) →
        edge-Undirected-Graph G p ≃ VE (map-equiv-unordered-pair e p))
      ( is-contr-total-equiv (vertex-Undirected-Graph G))
      ( pair (vertex-Undirected-Graph G) id-equiv)
      ( is-contr-total-Eq-Π
        ( λ p X → (edge-Undirected-Graph G p) ≃ X)
        ( λ p → is-contr-total-equiv (edge-Undirected-Graph G p)))

  is-equiv-equiv-eq-Undirected-Graph :
    (H : Undirected-Graph l1 l2) → is-equiv (equiv-eq-Undirected-Graph H)
  is-equiv-equiv-eq-Undirected-Graph =
    fundamental-theorem-id
      ( is-contr-total-equiv-Undirected-Graph)
      ( equiv-eq-Undirected-Graph)

  extensionality-Undirected-Graph :
    (H : Undirected-Graph l1 l2) → Id G H ≃ equiv-Undirected-Graph G H
  pr1 (extensionality-Undirected-Graph H) = equiv-eq-Undirected-Graph H
  pr2 (extensionality-Undirected-Graph H) = is-equiv-equiv-eq-Undirected-Graph H

  eq-equiv-Undirected-Graph :
    (H : Undirected-Graph l1 l2) → equiv-Undirected-Graph G H → Id G H
  eq-equiv-Undirected-Graph H =
    map-inv-is-equiv (is-equiv-equiv-eq-Undirected-Graph H)
```
