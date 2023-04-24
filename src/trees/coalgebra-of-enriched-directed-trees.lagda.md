# The coalgebra of enriched directed trees

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module trees.coalgebra-of-enriched-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import trees.coalgebras-polynomial-endofunctors
open import trees.enriched-directed-trees
open import trees.fibers-enriched-directed-trees
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
  {l1 l2 : Level} (l3 l4 : Level) (A : UU l1) (B : A → UU l2)
  where

  coalgebra-Enriched-Directed-Tree :
    coalgebra-polynomial-endofunctor (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4) A B
  pr1 coalgebra-Enriched-Directed-Tree = Enriched-Directed-Tree l3 l4 A B
  pr1 (pr2 coalgebra-Enriched-Directed-Tree T) =
    shape-root-Enriched-Directed-Tree A B T
  pr2 (pr2 coalgebra-Enriched-Directed-Tree T) b =
    {!fiber-base-Enriched-Directed-Tree A B T b!}
```
