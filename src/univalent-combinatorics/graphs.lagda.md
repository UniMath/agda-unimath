---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.graphs where

open import univalent-combinatorics.unordered-pairs public

Undirected-Graph : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Undirected-Graph l1 l2 = Σ (UU l1) (λ V → unordered-pair V → UU l2)

module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  vertex-Undirected-Graph : UU l1
  vertex-Undirected-Graph = pr1 G

  unordered-pair-vertices-Undirected-Graph : UU (lsuc lzero ⊔ l1)
  unordered-pair-vertices-Undirected-Graph =
    unordered-pair vertex-Undirected-Graph

  edge-Undirected-Graph : unordered-pair-vertices-Undirected-Graph → UU l2
  edge-Undirected-Graph = pr2 G

module _
  {l1 l2 l3 l4 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  where

  hom-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Undirected-Graph =
    Σ ( vertex-Undirected-Graph G → vertex-Undirected-Graph H)
      ( λ f →
        ( p : unordered-pair-vertices-Undirected-Graph G) →
        edge-Undirected-Graph G p →
        edge-Undirected-Graph H (map-unordered-pair f p))

  vertex-hom-Undirected-Graph :
    hom-Undirected-Graph → vertex-Undirected-Graph G → vertex-Undirected-Graph H
  vertex-hom-Undirected-Graph f = pr1 f

  unordered-pair-vertices-hom-Undirected-Graph :
    hom-Undirected-Graph →
    unordered-pair-vertices-Undirected-Graph G →
    unordered-pair-vertices-Undirected-Graph H
  unordered-pair-vertices-hom-Undirected-Graph f =
    map-unordered-pair (vertex-hom-Undirected-Graph f)

  edge-hom-Undirected-Graph :
    (f : hom-Undirected-Graph)
    (p : unordered-pair-vertices-Undirected-Graph G) →
    edge-Undirected-Graph G p →
    edge-Undirected-Graph H
      ( unordered-pair-vertices-hom-Undirected-Graph f p)
  edge-hom-Undirected-Graph f = pr2 f

  htpy-hom-Undirected-Graph :
    (f g : hom-Undirected-Graph) → UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-Undirected-Graph f g =
    Σ ( vertex-hom-Undirected-Graph f ~ vertex-hom-Undirected-Graph g)
      ( λ α →
        ( p : unordered-pair-vertices-Undirected-Graph G) →
        ( e : edge-Undirected-Graph G p) →
        Id ( tr
             ( edge-Undirected-Graph H)
             ( htpy-unordered-pair α p)
             ( edge-hom-Undirected-Graph f p e))
           ( edge-hom-Undirected-Graph g p e))

  refl-htpy-hom-Undirected-Graph :
    (f : hom-Undirected-Graph) → htpy-hom-Undirected-Graph f f
  pr1 (refl-htpy-hom-Undirected-Graph f) = refl-htpy
  pr2 (refl-htpy-hom-Undirected-Graph f) p e =
    ap ( λ t → tr (edge-Undirected-Graph H) t (edge-hom-Undirected-Graph f p e))
       ( preserves-refl-htpy-unordered-pair (vertex-hom-Undirected-Graph f) p)

  htpy-eq-hom-Undirected-Graph :
    (f g : hom-Undirected-Graph) → Id f g → htpy-hom-Undirected-Graph f g
  htpy-eq-hom-Undirected-Graph f .f refl = refl-htpy-hom-Undirected-Graph f

  abstract
    is-contr-total-htpy-hom-Undirected-Graph :
      (f : hom-Undirected-Graph) →
      is-contr (Σ (hom-Undirected-Graph) (htpy-hom-Undirected-Graph f))
    is-contr-total-htpy-hom-Undirected-Graph f =
      is-contr-total-Eq-structure
        ( λ gV gE α →
          ( p : unordered-pair-vertices-Undirected-Graph G) →
          ( e : edge-Undirected-Graph G p) →
          Id ( tr
               ( edge-Undirected-Graph H)
               ( htpy-unordered-pair α p)
               ( edge-hom-Undirected-Graph f p e))
             ( gE p e))
        ( is-contr-total-htpy (vertex-hom-Undirected-Graph f))
        ( pair (vertex-hom-Undirected-Graph f) refl-htpy)
        ( is-contr-equiv'
          ( Σ ( (p : unordered-pair-vertices-Undirected-Graph G) →
                edge-Undirected-Graph G p →
                edge-Undirected-Graph H
                  ( unordered-pair-vertices-hom-Undirected-Graph f p))
              ( λ gE →
                (p : unordered-pair-vertices-Undirected-Graph G) →
                (e : edge-Undirected-Graph G p) →
                Id (edge-hom-Undirected-Graph f p e) (gE p e)))
          ( equiv-tot
            ( λ gE →
              equiv-map-Π
                ( λ p →
                  equiv-map-Π
                    ( λ e →
                      equiv-concat
                        ( pr2 (refl-htpy-hom-Undirected-Graph f) p e)
                        ( gE p e)))))
          ( is-contr-total-Eq-Π
            ( λ p gE →
              ( e : edge-Undirected-Graph G p) →
              Id (edge-hom-Undirected-Graph f p e) (gE e))
            ( λ p → is-contr-total-htpy (edge-hom-Undirected-Graph f p))))

  is-equiv-htpy-eq-hom-Undirected-Graph :
    (f g : hom-Undirected-Graph) → is-equiv (htpy-eq-hom-Undirected-Graph f g)
  is-equiv-htpy-eq-hom-Undirected-Graph f =
    fundamental-theorem-id f
      ( refl-htpy-hom-Undirected-Graph f)
      ( is-contr-total-htpy-hom-Undirected-Graph f)
      ( htpy-eq-hom-Undirected-Graph f)

  extensionality-hom-Undirected-Graph :
    (f g : hom-Undirected-Graph) → Id f g ≃ htpy-hom-Undirected-Graph f g
  pr1 (extensionality-hom-Undirected-Graph f g) =
    htpy-eq-hom-Undirected-Graph f g
  pr2 (extensionality-hom-Undirected-Graph f g) =
    is-equiv-htpy-eq-hom-Undirected-Graph f g

  eq-htpy-hom-Undirected-Graph :
    (f g : hom-Undirected-Graph) → htpy-hom-Undirected-Graph f g → Id f g
  eq-htpy-hom-Undirected-Graph f g =
    map-inv-is-equiv (is-equiv-htpy-eq-hom-Undirected-Graph f g)

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

  hom-equiv-Undirected-Graph :
    equiv-Undirected-Graph → hom-Undirected-Graph
  pr1 (hom-equiv-Undirected-Graph f) = vertex-equiv-Undirected-Graph f
  pr2 (hom-equiv-Undirected-Graph f) = edge-equiv-Undirected-Graph f

  htpy-equiv-Undirected-Graph :
    (f g : equiv-Undirected-Graph) → UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-equiv-Undirected-Graph f g =
    htpy-hom-Undirected-Graph
      ( hom-equiv-Undirected-Graph f)
      ( hom-equiv-Undirected-Graph g)

  refl-htpy-equiv-Undirected-Graph :
    (f : equiv-Undirected-Graph) → htpy-equiv-Undirected-Graph f f
  refl-htpy-equiv-Undirected-Graph f =
    refl-htpy-hom-Undirected-Graph (hom-equiv-Undirected-Graph f)

  htpy-eq-equiv-Undirected-Graph :
    (f g : equiv-Undirected-Graph) → Id f g → htpy-equiv-Undirected-Graph f g
  htpy-eq-equiv-Undirected-Graph f .f refl = refl-htpy-equiv-Undirected-Graph f

  is-contr-total-htpy-equiv-Undirected-Graph :
    (f : equiv-Undirected-Graph) →
    is-contr (Σ (equiv-Undirected-Graph) (htpy-equiv-Undirected-Graph f))
  is-contr-total-htpy-equiv-Undirected-Graph f =
    is-contr-total-Eq-structure
      ( λ gV gE α →
        ( p : unordered-pair-vertices-Undirected-Graph G) →
          ( e : edge-Undirected-Graph G p) →
          Id ( tr
               ( edge-Undirected-Graph H)
               ( htpy-unordered-pair α p)
               ( edge-equiv-Undirected-Graph f p e))
             ( map-equiv (gE p) e))
      ( is-contr-total-htpy-equiv (equiv-vertex-equiv-Undirected-Graph f))
      ( pair (equiv-vertex-equiv-Undirected-Graph f) refl-htpy)
      ( is-contr-equiv'
        ( Σ ( (p : unordered-pair-vertices-Undirected-Graph G) →
              edge-Undirected-Graph G p ≃
              edge-Undirected-Graph H
                ( unordered-pair-vertices-equiv-Undirected-Graph f p))
            ( λ gE →
              (p : unordered-pair-vertices-Undirected-Graph G) →
              (e : edge-Undirected-Graph G p) →
              Id (edge-equiv-Undirected-Graph f p e) (map-equiv (gE p) e)))
        ( equiv-tot
          ( λ gE →
            equiv-map-Π
              ( λ p →
                equiv-map-Π
                  ( λ e →
                    equiv-concat
                      ( pr2 (refl-htpy-equiv-Undirected-Graph f) p e)
                      ( map-equiv (gE p) e)))))
        ( is-contr-total-Eq-Π
          ( λ p e →
            htpy-equiv
              ( equiv-edge-equiv-Undirected-Graph f p)
              ( e))
          ( λ p →
            is-contr-total-htpy-equiv (equiv-edge-equiv-Undirected-Graph f p))))

  is-equiv-htpy-eq-equiv-Undirected-Graph :
    (f g : equiv-Undirected-Graph) →
    is-equiv (htpy-eq-equiv-Undirected-Graph f g)
  is-equiv-htpy-eq-equiv-Undirected-Graph f =
    fundamental-theorem-id f
      ( refl-htpy-equiv-Undirected-Graph f)
      ( is-contr-total-htpy-equiv-Undirected-Graph f)
      ( htpy-eq-equiv-Undirected-Graph f)

  extensionality-equiv-Undirected-Graph :
    (f g : equiv-Undirected-Graph) → Id f g ≃ htpy-equiv-Undirected-Graph f g
  pr1 (extensionality-equiv-Undirected-Graph f g) =
    htpy-eq-equiv-Undirected-Graph f g
  pr2 (extensionality-equiv-Undirected-Graph f g) =
    is-equiv-htpy-eq-equiv-Undirected-Graph f g

  eq-htpy-equiv-Undirected-Graph :
    (f g : equiv-Undirected-Graph) → htpy-equiv-Undirected-Graph f g → Id f g
  eq-htpy-equiv-Undirected-Graph f g =
    map-inv-is-equiv (is-equiv-htpy-eq-equiv-Undirected-Graph f g)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  (K : Undirected-Graph l5 l6)
  where

  comp-hom-Undirected-Graph :
    hom-Undirected-Graph H K → hom-Undirected-Graph G H →
    hom-Undirected-Graph G K
  pr1 (comp-hom-Undirected-Graph (pair gV gE) (pair fV fE)) = gV ∘ fV
  pr2 (comp-hom-Undirected-Graph (pair gV gE) (pair fV fE)) p e =
    gE (map-unordered-pair fV p) (fE p e)

module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  id-hom-Undirected-Graph : hom-Undirected-Graph G G
  pr1 id-hom-Undirected-Graph = id
  pr2 id-hom-Undirected-Graph p = id

  id-equiv-Undirected-Graph : equiv-Undirected-Graph G G
  pr1 id-equiv-Undirected-Graph = id-equiv
  pr2 id-equiv-Undirected-Graph p = id-equiv

  equiv-eq-Undirected-Graph :
    (H : Undirected-Graph l1 l2) → Id G H → equiv-Undirected-Graph G H
  equiv-eq-Undirected-Graph .G refl = id-equiv-Undirected-Graph

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
    fundamental-theorem-id G
      id-equiv-Undirected-Graph
      is-contr-total-equiv-Undirected-Graph
      equiv-eq-Undirected-Graph

  extensionality-Undirected-Graph :
    (H : Undirected-Graph l1 l2) → Id G H ≃ equiv-Undirected-Graph G H
  pr1 (extensionality-Undirected-Graph H) = equiv-eq-Undirected-Graph H
  pr2 (extensionality-Undirected-Graph H) = is-equiv-equiv-eq-Undirected-Graph H

  eq-equiv-Undirected-Graph :
    (H : Undirected-Graph l1 l2) → equiv-Undirected-Graph G H → Id G H
  eq-equiv-Undirected-Graph H =
    map-inv-is-equiv (is-equiv-equiv-eq-Undirected-Graph H)

module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  orientation-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2)
  orientation-Undirected-Graph =
    ( p : unordered-pair-vertices-Undirected-Graph G) →
    edge-Undirected-Graph G p → type-UU-Fin (pr1 p)

  source-edge-orientation-Undirected-Graph :
    orientation-Undirected-Graph →
    (p : unordered-pair-vertices-Undirected-Graph G) →
    edge-Undirected-Graph G p → vertex-Undirected-Graph G
  source-edge-orientation-Undirected-Graph d (pair X p) e =
    p (d (pair X p) e)

module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  is-simple-Undirected-Graph-Prop : UU-Prop (lsuc lzero ⊔ l1 ⊔ l2)
  is-simple-Undirected-Graph-Prop =
    prod-Prop
      ( Π-Prop
        ( unordered-pair-vertices-Undirected-Graph G)
        ( λ p →
          function-Prop (edge-Undirected-Graph G p) (is-emb-Prop (pr2 p))))
      ( Π-Prop
        ( unordered-pair-vertices-Undirected-Graph G)
        ( λ p → is-prop-Prop (edge-Undirected-Graph G p)))

  is-simple-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2)
  is-simple-Undirected-Graph = type-Prop is-simple-Undirected-Graph-Prop

  is-prop-is-simple-Undirected-Graph : is-prop is-simple-Undirected-Graph
  is-prop-is-simple-Undirected-Graph =
    is-prop-type-Prop is-simple-Undirected-Graph-Prop
```
