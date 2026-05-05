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

Using the [fibers](trees.fibers-enriched-directed-trees.md) of
[base elements](trees.bases-enriched-directed-trees.md), the type of
[enriched directed trees](trees.enriched-directed-trees.md) has the structure of
a [coalgebra](trees.coalgebras-polynomial-endofunctors.md) for the
[polynomial endofunctor](trees.polynomial-endofunctors.md)

```text
  X ↦ Σ (a : A), (B a → X).
```

## Definition

```agda
module _
  {l1 l2 : Level} (l3 : Level) (P@(A , B) : polynomial-endofunctor l1 l2)
  where

  structure-coalgebra-Enriched-Directed-Tree :
    Enriched-Directed-Tree l3 l3 A B →
    type-polynomial-endofunctor P (Enriched-Directed-Tree l3 l3 A B)
  structure-coalgebra-Enriched-Directed-Tree T =
    ( shape-root-Enriched-Directed-Tree A B T ,
      fiber-base-Enriched-Directed-Tree A B T)

  coalgebra-Enriched-Directed-Tree :
    coalgebra-polynomial-endofunctor (l1 ⊔ l2 ⊔ lsuc l3) P
  coalgebra-Enriched-Directed-Tree =
    ( Enriched-Directed-Tree l3 l3 A B ,
      structure-coalgebra-Enriched-Directed-Tree)
```
