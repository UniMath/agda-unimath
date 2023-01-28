---
title: Morphisms of directed graphs
---

```agda
module graph-theory.morphisms-directed-graphs where

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.directed-graphs
```

## Definitions

### Morphisms graphs

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Graph l1 l2) (H : Graph l3 l4)
  where

  hom-Graph : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Graph =
    Σ ( vertex-Graph G → vertex-Graph H )
      λ α → (x y : vertex-Graph G) → (e : edge-Graph G x y)
          → edge-Graph H (α x) (α y)

  module _ (f : hom-Graph) where

    vertex-hom-Graph : vertex-Graph G → vertex-Graph H
    vertex-hom-Graph = pr1 f

    edge-hom-Graph :
      {x y : vertex-Graph G} (e : edge-Graph G x y) →
      edge-Graph H (vertex-hom-Graph x) (vertex-hom-Graph y)
    edge-hom-Graph {x} {y} e = pr2 f x y e
```

### Composition of morphisms graphs

```agda

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (G : Graph l1 l2) (H : Graph l3 l4)
  (K : Graph l5 l6)
  where

  comp-hom-Graph :
    hom-Graph H K → hom-Graph G H →
    hom-Graph G K
  pr1 (comp-hom-Graph g f) = (vertex-hom-Graph H K g) ∘ (vertex-hom-Graph G H f)
  pr2 (comp-hom-Graph g f) = λ x y e → (edge-hom-Graph H K g) (β e)
    where
    α = vertex-hom-Graph G H f
    β = edge-hom-Graph G H f
```

### Identity morphisms graphs

```agda
module _
  {l1 l2 : Level} (G : Graph l1 l2)
  where

  id-hom-Graph : hom-Graph G G
  pr1 id-hom-Graph = id
  pr2 id-hom-Graph _ _ = id
```


## Properties

### Characterizing the identity type of morphisms graphs

```agda
{-
module _
  {l1 l2 l3 l4 : Level}
  (G : Graph l1 l2) (H : Graph l3 l4)
  where

  htpy-hom-Graph :
    (f g : hom-Graph G H) → UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-Graph f g =
    Σ ( vertex-hom-Graph G H f ~ vertex-hom-Graph G H g)
      ( λ α →
        ( p : unordered-pair-vertices-Graph G) →
        ( e : edge-Graph G p) →
        Id ( tr
             ( edge-Graph H)
             ( htpy-unordered-pair α p)
             ( edge-hom-Graph G H f p e))
           ( edge-hom-Graph G H g p e))

  refl-htpy-hom-Graph :
    (f : hom-Graph G H) → htpy-hom-Graph f f
  pr1 (refl-htpy-hom-Graph f) = refl-htpy
  pr2 (refl-htpy-hom-Graph f) p e =
    ap ( λ t →
         tr (edge-Graph H) t (edge-hom-Graph G H f p e))
       ( preserves-refl-htpy-unordered-pair
         ( vertex-hom-Graph G H f) p)

  htpy-eq-hom-Graph :
    (f g : hom-Graph G H) → Id f g → htpy-hom-Graph f g
  htpy-eq-hom-Graph f .f refl = refl-htpy-hom-Graph f

  abstract
    is-contr-total-htpy-hom-Graph :
      (f : hom-Graph G H) →
      is-contr (Σ (hom-Graph G H) (htpy-hom-Graph f))
    is-contr-total-htpy-hom-Graph f =
      is-contr-total-Eq-structure
        ( λ gV gE α →
          ( p : unordered-pair-vertices-Graph G) →
          ( e : edge-Graph G p) →
          Id ( tr
               ( edge-Graph H)
               ( htpy-unordered-pair α p)
               ( edge-hom-Graph G H f p e))
             ( gE p e))
        ( is-contr-total-htpy (vertex-hom-Graph G H f))
        ( pair (vertex-hom-Graph G H f) refl-htpy)
        ( is-contr-equiv'
          ( Σ ( (p : unordered-pair-vertices-Graph G) →
                edge-Graph G p →
                edge-Graph H
                  ( unordered-pair-vertices-hom-Graph G H f p))
              ( λ gE →
                (p : unordered-pair-vertices-Graph G) →
                (e : edge-Graph G p) →
                Id (edge-hom-Graph G H f p e) (gE p e)))
          ( equiv-tot
            ( λ gE →
              equiv-map-Π
                ( λ p →
                  equiv-map-Π
                    ( λ e →
                      equiv-concat
                        ( pr2 (refl-htpy-hom-Graph f) p e)
                        ( gE p e)))))
          ( is-contr-total-Eq-Π
            ( λ p gE →
              ( e : edge-Graph G p) →
              Id (edge-hom-Graph G H f p e) (gE e))
            ( λ p → is-contr-total-htpy (edge-hom-Graph G H f p))))

  is-equiv-htpy-eq-hom-Graph :
    (f g : hom-Graph G H) →
    is-equiv (htpy-eq-hom-Graph f g)
  is-equiv-htpy-eq-hom-Graph f =
    fundamental-theorem-id f
      ( refl-htpy-hom-Graph f)
      ( is-contr-total-htpy-hom-Graph f)
      ( htpy-eq-hom-Graph f)

  extensionality-hom-Graph :
    (f g : hom-Graph G H) → Id f g ≃ htpy-hom-Graph f g
  pr1 (extensionality-hom-Graph f g) =
    htpy-eq-hom-Graph f g
  pr2 (extensionality-hom-Graph f g) =
    is-equiv-htpy-eq-hom-Graph f g

  eq-htpy-hom-Graph :
    (f g : hom-Graph G H) → htpy-hom-Graph f g → Id f g
  eq-htpy-hom-Graph f g =
    map-inv-is-equiv (is-equiv-htpy-eq-hom-Graph f g)
-}
```
