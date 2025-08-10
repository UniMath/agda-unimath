# The combinator of full binary trees

```agda
module trees.combinator-full-binary-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications

open import structured-types.magmas

open import trees.full-binary-trees
open import trees.labeled-full-binary-trees
```

</details>

## Idea

Two [full binary trees](trees.full-binary-trees.md) `L, R` may be combined into
a new full binary tree in the natural way. This extends to a combinator of
[labeled full binary trees](trees.labeled-full-binary-trees.md). These form an
important class of [magmas](structured-types.magmas.md), cf.
[the free magma on one generator](trees.free-magma-on-one-generator.md) and
[free magmas on types](trees.free-magmas-on-types.md).

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

### The magmas of full binary trees and labeled full binary trees

```agda
full-binary-tree-Magma : Magma lzero
pr1 full-binary-tree-Magma = full-binary-tree
pr2 full-binary-tree-Magma = combinator-full-binary-tree

labeled-full-binary-tree-Magma : {l : Level} (X : UU l) → Magma l
pr1 (labeled-full-binary-tree-Magma X) = labeled-full-binary-tree X
pr2 (labeled-full-binary-tree-Magma X) = combinator-labeled-full-binary-tree X
```

## Properties

### The combinator of labeled full binary trees commutes with branches

That is, for binary trees `L R : full-binary-tree` and an `X`-labeling `lab` of
`join-full-binary-tree L R`, we have

```text
  combinator-labeled-full-binary-tree X (L , λ x → lab (inl x)) (R , λ x → lab (inr x))
  =
  (( join-full-binary-tree L R) , lab)
```

```agda
module _
  {l : Level} (X : UU l) (L R : full-binary-tree)
  (lab : labeling-full-binary-tree X (join-full-binary-tree L R))
  where

  htpy-combinator-commutes-with-labelings-full-binary-tree :
    tr (labeling-full-binary-tree X) refl
      ( pr2 (combinator-labeled-full-binary-tree X
      ( L , λ x → lab (inl x)) (R , (λ x → lab (inr x))))) ~
    lab
  htpy-combinator-commutes-with-labelings-full-binary-tree (inl x) = refl
  htpy-combinator-commutes-with-labelings-full-binary-tree (inr x) = refl

  combinator-commutes-with-labelings-full-binary-tree :
    combinator-labeled-full-binary-tree X
      ( L , (λ x → lab (inl x))) (R , (λ x → lab (inr x))) ＝
    ( join-full-binary-tree L R , lab)
  combinator-commutes-with-labelings-full-binary-tree =
    eq-pair-Σ refl
    ( eq-htpy htpy-combinator-commutes-with-labelings-full-binary-tree)
```
