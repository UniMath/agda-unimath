# The combinator of full binary trees

```agda
module trees.combinator-full-binary-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.universe-levels

open import structured-types.magmas

open import trees.full-binary-trees
open import trees.labeled-full-binary-trees
```

</details>

## Idea

Two [full binary trees](trees.full-binary-trees.md) `L, R` may be combined into
a new full binary tree in the natural way. By abstract nonsense, this extends to
a combinator of [labeled full binary trees](trees.labeled-full-binary-trees.md).
These form an important class of [magmas](structured-types.magmas.md), cf.
[the free magma on one generator](trees.free-magma-on-one-generator.md).

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
