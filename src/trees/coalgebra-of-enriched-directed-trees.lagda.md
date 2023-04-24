# The coalgebra of enriched directed trees

```agda
{-# OPTIONS --lossy-unification --allow-unsolved-metas #-}

module trees.coalgebra-of-enriched-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import trees.coalgebras-polynomial-endofunctors
open import trees.enriched-directed-trees
open import trees.equivalences-enriched-directed-trees
open import trees.fibers-enriched-directed-trees
open import trees.morphisms-coalgebras-polynomial-endofunctors
open import trees.polynomial-endofunctors
open import trees.underlying-trees-elements-coalgebras-polynomial-endofunctors
```

</details>

## Idea

Using the fibers of base elements, the type of enriched directed trees has the
structure of a coalgebra for the polynomial endofunctor

```md
  X ↦ Σ (a : A), B a → X.
```

## Definition

```agda
module _
  {l1 l2 : Level} (l3 : Level) (A : UU l1) (B : A → UU l2)
  where

  structure-coalgebra-Enriched-Directed-Tree :
    Enriched-Directed-Tree l3 l3 A B →
    type-polynomial-endofunctor A B (Enriched-Directed-Tree l3 l3 A B)
  pr1 (structure-coalgebra-Enriched-Directed-Tree T) =
    shape-root-Enriched-Directed-Tree A B T
  pr2 (structure-coalgebra-Enriched-Directed-Tree T) =
    fiber-base-Enriched-Directed-Tree A B T

  coalgebra-Enriched-Directed-Tree :
    coalgebra-polynomial-endofunctor (l1 ⊔ l2 ⊔ lsuc l3) A B
  pr1 coalgebra-Enriched-Directed-Tree = Enriched-Directed-Tree l3 l3 A B
  pr2 coalgebra-Enriched-Directed-Tree =
    structure-coalgebra-Enriched-Directed-Tree
```

## Properties

### The coalgebra of enriched directed trees is terminal

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : coalgebra-polynomial-endofunctor l3 A B)
  where

  map-hom-coalgebra-Enriched-Directed-Tree :
    type-coalgebra-polynomial-endofunctor X →
    Enriched-Directed-Tree (l2 ⊔ l3) (l2 ⊔ l3) A B
  map-hom-coalgebra-Enriched-Directed-Tree =
    enriched-directed-tree-element-coalgebra X

  structure-hom-coalgebra-Enriched-Directed-Tree :
    coherence-square-maps
      ( map-hom-coalgebra-Enriched-Directed-Tree)
      ( structure-coalgebra-polynomial-endofunctor X)
      ( structure-coalgebra-Enriched-Directed-Tree (l2 ⊔ l3) A B)
      ( map-polynomial-endofunctor A B map-hom-coalgebra-Enriched-Directed-Tree)
  structure-hom-coalgebra-Enriched-Directed-Tree x =
    eq-Eq-type-polynomial-endofunctor
      ( map-polynomial-endofunctor A B
        ( map-hom-coalgebra-Enriched-Directed-Tree)
        ( structure-coalgebra-polynomial-endofunctor X x))
      ( structure-coalgebra-Enriched-Directed-Tree (l2 ⊔ l3) A B
        ( map-hom-coalgebra-Enriched-Directed-Tree x))
      ( refl ,
        λ b →
        eq-equiv-Enriched-Directed-Tree A B
          ( enriched-directed-tree-element-coalgebra X
            ( component-coalgebra-polynomial-endofunctor X x b))
          ( fiber-base-Enriched-Directed-Tree A B
            ( enriched-directed-tree-element-coalgebra X x)
            ( b))
          {!!})

  hom-coalgebra-Enriched-Directed-Tree :
    hom-coalgebra-polynomial-endofunctor X
      ( coalgebra-Enriched-Directed-Tree (l2 ⊔ l3) A B)
  pr1 hom-coalgebra-Enriched-Directed-Tree =
    map-hom-coalgebra-Enriched-Directed-Tree
  pr2 hom-coalgebra-Enriched-Directed-Tree = {!!}
```
