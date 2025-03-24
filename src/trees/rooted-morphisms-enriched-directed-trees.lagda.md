# Rooted morphisms of enriched directed trees

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module trees.rooted-morphisms-enriched-directed-trees
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.function-types funext
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.propositions funext univalence
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import trees.enriched-directed-trees funext univalence truncations
open import trees.morphisms-enriched-directed-trees funext univalence truncations
open import trees.rooted-morphisms-directed-trees funext univalence truncations
```

</details>

## Idea

**Rooted morphisms of enriched directed trees** are root preserving morphisms of
enriched directed trees.

## Definitions

### Rooted morphisms of directed trees

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (A : UU l1) (B : A → UU l2)
  (S : Enriched-Directed-Tree l3 l4 A B)
  (T : Enriched-Directed-Tree l5 l6 A B)
  where

  preserves-root-hom-enriched-directed-tree-Prop :
    hom-Enriched-Directed-Tree A B S T → Prop l5
  preserves-root-hom-enriched-directed-tree-Prop f =
    preserves-root-hom-directed-tree-Prop
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( directed-tree-hom-Enriched-Directed-Tree A B S T f)

  preserves-root-hom-Enriched-Directed-Tree :
    hom-Enriched-Directed-Tree A B S T → UU l5
  preserves-root-hom-Enriched-Directed-Tree f =
    preserves-root-hom-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( directed-tree-hom-Enriched-Directed-Tree A B S T f)

  is-prop-preserves-root-hom-Enriched-Directed-Tree :
    (f : hom-Enriched-Directed-Tree A B S T) →
    is-prop (preserves-root-hom-Enriched-Directed-Tree f)
  is-prop-preserves-root-hom-Enriched-Directed-Tree f =
    is-prop-preserves-root-hom-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B S)
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( directed-tree-hom-Enriched-Directed-Tree A B S T f)

  rooted-hom-Enriched-Directed-Tree : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  rooted-hom-Enriched-Directed-Tree =
    Σ ( hom-Enriched-Directed-Tree A B S T)
      ( preserves-root-hom-Enriched-Directed-Tree)

  module _
    (f : rooted-hom-Enriched-Directed-Tree)
    where

    hom-rooted-hom-Enriched-Directed-Tree : hom-Enriched-Directed-Tree A B S T
    hom-rooted-hom-Enriched-Directed-Tree = pr1 f

    node-rooted-hom-Enriched-Directed-Tree :
      node-Enriched-Directed-Tree A B S → node-Enriched-Directed-Tree A B T
    node-rooted-hom-Enriched-Directed-Tree =
      node-hom-Enriched-Directed-Tree A B S T
        ( hom-rooted-hom-Enriched-Directed-Tree)

    edge-rooted-hom-Enriched-Directed-Tree :
      {x y : node-Enriched-Directed-Tree A B S} →
      edge-Enriched-Directed-Tree A B S x y →
      edge-Enriched-Directed-Tree A B T
        ( node-rooted-hom-Enriched-Directed-Tree x)
        ( node-rooted-hom-Enriched-Directed-Tree y)
    edge-rooted-hom-Enriched-Directed-Tree =
      edge-hom-Enriched-Directed-Tree A B S T
        ( hom-rooted-hom-Enriched-Directed-Tree)

    direct-predecessor-rooted-hom-Enriched-Directed-Tree :
      (x : node-Enriched-Directed-Tree A B S) →
      Σ ( node-Enriched-Directed-Tree A B S)
        ( λ y → edge-Enriched-Directed-Tree A B S y x) →
      Σ ( node-Enriched-Directed-Tree A B T)
        ( λ y →
          edge-Enriched-Directed-Tree A B T y
            ( node-rooted-hom-Enriched-Directed-Tree x))
    direct-predecessor-rooted-hom-Enriched-Directed-Tree =
      direct-predecessor-hom-Enriched-Directed-Tree A B S T
        ( hom-rooted-hom-Enriched-Directed-Tree)

    shape-rooted-hom-Enriched-Directed-Tree :
      ( shape-Enriched-Directed-Tree A B S) ~
      ( ( shape-Enriched-Directed-Tree A B T) ∘
        ( node-rooted-hom-Enriched-Directed-Tree))
    shape-rooted-hom-Enriched-Directed-Tree =
      shape-hom-Enriched-Directed-Tree A B S T
        ( hom-rooted-hom-Enriched-Directed-Tree)

    enrichment-rooted-hom-Enriched-Directed-Tree :
      ( x : node-Enriched-Directed-Tree A B S) →
      ( ( direct-predecessor-rooted-hom-Enriched-Directed-Tree x) ∘
        ( map-enrichment-Enriched-Directed-Tree A B S x)) ~
      ( ( map-enrichment-Enriched-Directed-Tree A B T
          ( node-rooted-hom-Enriched-Directed-Tree x)) ∘
          ( tr B (shape-rooted-hom-Enriched-Directed-Tree x)))
    enrichment-rooted-hom-Enriched-Directed-Tree =
      enrichment-hom-Enriched-Directed-Tree A B S T
        ( hom-rooted-hom-Enriched-Directed-Tree)

    preserves-root-rooted-hom-Enriched-Directed-Tree :
      preserves-root-hom-Enriched-Directed-Tree
        hom-rooted-hom-Enriched-Directed-Tree
    preserves-root-rooted-hom-Enriched-Directed-Tree = pr2 f
```

### The identity rooted morphism of directed trees

```agda
id-rooted-hom-Enriched-Directed-Tree :
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  (T : Enriched-Directed-Tree l1 l2 A B) →
  rooted-hom-Enriched-Directed-Tree A B T T
pr1 (id-rooted-hom-Enriched-Directed-Tree A B T) =
  id-hom-Enriched-Directed-Tree A B T
pr2 (id-rooted-hom-Enriched-Directed-Tree A B T) = refl
```
