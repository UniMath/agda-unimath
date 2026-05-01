# Morphisms of enriched directed trees

```agda
module trees.morphisms-enriched-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import trees.enriched-directed-trees
open import trees.morphisms-directed-trees
```

</details>

## Idea

A
{{#concept "morphism" Disambiguation="of enriched directed trees" Agda=hom-Enriched-Directed-Tree}}
of [enriched directed trees](trees.enriched-directed-trees.md) is a
[morphism](trees.morphisms-directed-trees.md) of
[directed trees](trees.directed-trees.md) that preserves the enrichment
structure.

## Definitions

### Morphisms of enriched directed trees

```agda
hom-Enriched-Directed-Tree :
  {l1 l2 l3 l4 l5 l6 : Level} (A : UU l1) (B : A → UU l2) →
  Enriched-Directed-Tree l3 l4 A B → Enriched-Directed-Tree l5 l6 A B →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
hom-Enriched-Directed-Tree A B S T =
  Σ ( hom-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T))
    ( λ f →
      Σ ( coherence-triangle-maps
          ( shape-Enriched-Directed-Tree A B S)
          ( shape-Enriched-Directed-Tree A B T)
          ( node-hom-Directed-Tree
            ( directed-tree-Enriched-Directed-Tree A B S)
            ( directed-tree-Enriched-Directed-Tree A B T)
            ( f)))
        ( λ H →
          ( x : node-Enriched-Directed-Tree A B S) →
          coherence-square-maps
            ( tr B (H x))
            ( map-enrichment-Enriched-Directed-Tree A B S x)
            ( map-enrichment-Enriched-Directed-Tree A B T
              ( node-hom-Directed-Tree
                ( directed-tree-Enriched-Directed-Tree A B S)
                ( directed-tree-Enriched-Directed-Tree A B T)
                ( f)
                ( x)))
            ( direct-predecessor-hom-Directed-Tree
              ( directed-tree-Enriched-Directed-Tree A B S)
              ( directed-tree-Enriched-Directed-Tree A B T)
              ( f)
              ( x))))

module _
  {l1 l2 l3 l4 l5 l6 : Level} (A : UU l1) (B : A → UU l2)
  (S : Enriched-Directed-Tree l3 l4 A B) (T : Enriched-Directed-Tree l5 l6 A B)
  (f : hom-Enriched-Directed-Tree A B S T)
  where

  directed-tree-hom-Enriched-Directed-Tree :
    hom-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
  directed-tree-hom-Enriched-Directed-Tree = pr1 f

  node-hom-Enriched-Directed-Tree :
    node-Enriched-Directed-Tree A B S → node-Enriched-Directed-Tree A B T
  node-hom-Enriched-Directed-Tree =
    node-hom-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( directed-tree-hom-Enriched-Directed-Tree)

  edge-hom-Enriched-Directed-Tree :
    {x y : node-Enriched-Directed-Tree A B S} →
    edge-Enriched-Directed-Tree A B S x y →
    edge-Enriched-Directed-Tree A B T
      ( node-hom-Enriched-Directed-Tree x)
      ( node-hom-Enriched-Directed-Tree y)
  edge-hom-Enriched-Directed-Tree =
    edge-hom-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( directed-tree-hom-Enriched-Directed-Tree)

  direct-predecessor-hom-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree A B S) →
    Σ ( node-Enriched-Directed-Tree A B S)
      ( λ y → edge-Enriched-Directed-Tree A B S y x) →
    Σ ( node-Enriched-Directed-Tree A B T)
      ( λ y →
        edge-Enriched-Directed-Tree A B T y
          ( node-hom-Enriched-Directed-Tree x))
  direct-predecessor-hom-Enriched-Directed-Tree =
    direct-predecessor-hom-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( directed-tree-hom-Enriched-Directed-Tree)

  shape-hom-Enriched-Directed-Tree :
    coherence-triangle-maps
      ( shape-Enriched-Directed-Tree A B S)
      ( shape-Enriched-Directed-Tree A B T)
      ( node-hom-Enriched-Directed-Tree)
  shape-hom-Enriched-Directed-Tree = pr1 (pr2 f)

  enrichment-hom-Enriched-Directed-Tree :
    ( x : node-Enriched-Directed-Tree A B S) →
    coherence-square-maps
      ( tr B (shape-hom-Enriched-Directed-Tree x))
      ( map-enrichment-Enriched-Directed-Tree A B S x)
      ( map-enrichment-Enriched-Directed-Tree A B T
        ( node-hom-Directed-Tree
          ( directed-tree-Enriched-Directed-Tree A B S)
          ( directed-tree-Enriched-Directed-Tree A B T)
          ( directed-tree-hom-Enriched-Directed-Tree)
          ( x)))
      ( direct-predecessor-hom-Enriched-Directed-Tree x)
  enrichment-hom-Enriched-Directed-Tree = pr2 (pr2 f)
```

### Homotopies of morphisms of enriched directed trees

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (A : UU l1) (B : A → UU l2)
  (S : Enriched-Directed-Tree l3 l4 A B) (T : Enriched-Directed-Tree l5 l6 A B)
  (f g : hom-Enriched-Directed-Tree A B S T)
  where

  htpy-hom-Enriched-Directed-Tree : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  htpy-hom-Enriched-Directed-Tree =
    Σ ( htpy-hom-Directed-Tree
        ( directed-tree-Enriched-Directed-Tree A B S)
        ( directed-tree-Enriched-Directed-Tree A B T)
        ( directed-tree-hom-Enriched-Directed-Tree A B S T f)
        ( directed-tree-hom-Enriched-Directed-Tree A B S T g))
      ( λ H →
        Σ ( ( ( shape-hom-Enriched-Directed-Tree A B S T f) ∙h
              ( ( shape-Enriched-Directed-Tree A B T) ·l
                ( node-htpy-hom-Directed-Tree
                  ( directed-tree-Enriched-Directed-Tree A B S)
                  ( directed-tree-Enriched-Directed-Tree A B T)
                  ( directed-tree-hom-Enriched-Directed-Tree A B S T f)
                  ( directed-tree-hom-Enriched-Directed-Tree A B S T g)
                  ( H)))) ~
            ( shape-hom-Enriched-Directed-Tree A B S T g))
          ( λ K →
            ( x : node-Enriched-Directed-Tree A B S) →
            ( ( ( tot
                  ( λ y →
                    tr
                      ( edge-Enriched-Directed-Tree A B T y)
                      ( node-htpy-hom-Directed-Tree
                        ( directed-tree-Enriched-Directed-Tree A B S)
                        ( directed-tree-Enriched-Directed-Tree A B T)
                        ( directed-tree-hom-Enriched-Directed-Tree A B S T f)
                        ( directed-tree-hom-Enriched-Directed-Tree A B S T g)
                        ( H)
                        ( x)))) ·l
                ( enrichment-hom-Enriched-Directed-Tree A B S T f x)) ∙h
              ( ( ( coherence-square-map-enrichment-Enriched-Directed-Tree
                    A B T (pr1 H x)) ·r
                  ( tr B (shape-hom-Enriched-Directed-Tree A B S T f x))) ∙h
                ( λ b →
                  ap
                    ( map-enrichment-Enriched-Directed-Tree A B T
                      ( node-hom-Enriched-Directed-Tree A B S T g x))
                    ( ( inv
                        ( tr-concat
                          ( shape-hom-Enriched-Directed-Tree A B S T f x)
                          ( ap
                            ( shape-Enriched-Directed-Tree A B T)
                            ( pr1 H x))
                          ( b))) ∙
                      ( ap (λ q → tr B q b) (K x)))))) ~
            ( ( ( direct-predecessor-htpy-hom-Directed-Tree
                  ( directed-tree-Enriched-Directed-Tree A B S)
                  ( directed-tree-Enriched-Directed-Tree A B T)
                  ( directed-tree-hom-Enriched-Directed-Tree A B S T f)
                  ( directed-tree-hom-Enriched-Directed-Tree A B S T g)
                  ( H)
                  ( x)) ·r
                ( map-enrichment-Enriched-Directed-Tree A B S x)) ∙h
              ( enrichment-hom-Enriched-Directed-Tree A B S T g x))))
```

### Identity morphisms of enriched directed trees

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  (T : Enriched-Directed-Tree l3 l4 A B)
  where

  id-hom-Enriched-Directed-Tree :
    hom-Enriched-Directed-Tree A B T T
  pr1 id-hom-Enriched-Directed-Tree =
    id-hom-Directed-Tree (directed-tree-Enriched-Directed-Tree A B T)
  pr1 (pr2 id-hom-Enriched-Directed-Tree) = refl-htpy
  pr2 (pr2 id-hom-Enriched-Directed-Tree) x = refl-htpy
```
