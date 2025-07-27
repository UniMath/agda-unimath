# The combinator of full binary trees

```agda
module trees.combinator-full-binary-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.isolated-elements
open import foundation.maybe
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.morphisms-directed-graphs
open import graph-theory.walks-directed-graphs

open import trees.bases-directed-trees
open import trees.directed-trees
open import trees.equivalences-directed-trees
open import trees.fibers-directed-trees
open import trees.full-binary-trees
open import trees.labeled-full-binary-trees
open import trees.morphisms-directed-trees

open import elementary-number-theory.natural-numbers

open import foundation.empty-types
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types

open import structured-types.magmas
```

</details>

## Idea

Two [full binary trees](trees.full-binary-trees.md) `L, R` may be combined into
a new full binary tree in the natural way. By abstract nonsense, this extends to
a combinator of [labeled full binary trees](trees.labeled-full-binary-trees.md).
These form an important class of [magmas](structured-types.magmas.md).

## Definition

```agda
combinator-full-binary-tree :
  full-binary-tree → full-binary-tree → full-binary-tree
combinator-full-binary-tree L R = join-full-binary-tree L R

combinator-labeled-full-binary-tree :
  {l : Level} (X : UU l) → labeled-full-binary-tree X →
  labeled-full-binary-tree X → labeled-full-binary-tree X
pr1 (combinator-labeled-full-binary-tree X (L , _) (R , _)) =
  combinator-full-binary-tree L R
pr2 (combinator-labeled-full-binary-tree X (L , L-label) (R , _)) (inl x) =
  L-label x
pr2 (combinator-labeled-full-binary-tree X (L , _) (R , R-label)) (inr x) =
  R-label x
```

## The magmas of full binary trees and labeled full binary trees

```agda
full-binary-tree-Magma : Magma lzero
pr1 full-binary-tree-Magma = full-binary-tree
pr2 full-binary-tree-Magma = combinator-full-binary-tree

labeled-full-binary-tree-Magma : {l : Level} (X : UU l) → Magma l
pr1 (labeled-full-binary-tree-Magma X) = labeled-full-binary-tree X
pr2 (labeled-full-binary-tree-Magma X) = combinator-labeled-full-binary-tree X
```
