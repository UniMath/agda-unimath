# The coalgebra of enriched directed trees

```agda
{-# OPTIONS --lossy-unification #-}

module trees.coalgebra-of-enriched-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import trees.coalgebras-polynomial-endofunctors
open import trees.enriched-directed-trees
open import trees.fibers-enriched-directed-trees
open import trees.polynomial-endofunctors
```

</details>

## Idea

Using the fibers of base elements, the type of enriched directed trees has the
structure of a coalgebra for the polynomial endofunctor

```text
  X ↦ Σ (a : A), B a → X.
```

## Definition

```agda
module _
  {l1 l2 : Level} (l3 : Level) (A : UU l1) (B : A → UU l2)
  where

  structure-coalgebra-Enriched-Directed-Tree :
    Enriched-Directed-Tree l3 l3 A B →
    type-polynomial-endofunctor' A B (Enriched-Directed-Tree l3 l3 A B)
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
