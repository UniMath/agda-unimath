# The coalgebra of directed trees

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module trees.coalgebra-of-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.universe-levels

open import trees.bases-directed-trees
open import trees.coalgebras-polynomial-endofunctors
open import trees.directed-trees
open import trees.fibers-directed-trees
open import trees.morphisms-coalgebras-polynomial-endofunctors
open import trees.underlying-trees-elements-coalgebras-polynomial-endofunctors
```

</details>

## Idea

Using the fibers of base elements, the type of directed trees, of which the type
of nodes and the types of edges are of the same universe level, has the
structure of a coalgebra for the polynomial endofunctor

```md
  A ↦ Σ (X : UU), X → A
```

## Definition

```agda
coalgebra-Directed-Tree :
  (l : Level) → coalgebra-polynomial-endofunctor (lsuc l) (UU l) (λ X → X)
pr1 (coalgebra-Directed-Tree l) = Directed-Tree l l
pr1 (pr2 (coalgebra-Directed-Tree l) T) = base-Directed-Tree T
pr2 (pr2 (coalgebra-Directed-Tree l) T) = fiber-base-Directed-Tree T
```

## Properties

### The coalgebra of directed trees is the terminal coalgebra of `A ↦ Σ (X : UU), X → A`

```agda
module _
  {l : Level} (X : coalgebra-polynomial-endofunctor l (UU l) id)
  where

  map-hom-coalgebra-Directed-Tree :
    type-coalgebra-polynomial-endofunctor X → Directed-Tree l l
  map-hom-coalgebra-Directed-Tree = directed-tree-element-coalgebra X

  hom-coalgebra-Directed-Tree :
    hom-coalgebra-polynomial-endofunctor X (coalgebra-Directed-Tree l)
  pr1 hom-coalgebra-Directed-Tree = {!!}
  pr2 hom-coalgebra-Directed-Tree = {!!}
```
