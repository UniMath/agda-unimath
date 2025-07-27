# The free magma on `X`

```agda
module trees.free-magmas-on-a-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.retractions
open import foundation-core.sections

open import structured-types.magmas
open import structured-types.morphisms-magmas

open import trees.combinator-full-binary-trees
open import trees.full-binary-trees
open import trees.labeled-full-binary-trees
```

</details>

## Idea

As the type of [full binary trees](trees.full-binary-trees.md) is the
[free magma on one generator](trees.free-magma-on-one-generator.md), so too is
the type of [`X`-labeled full binary trees](trees.labeled-full-binary-trees.md)
the **free magma on `X`**. That is, for any [magma](structured-types.magmas.md)
`M` and any type `X`, the map
`(hom-Magma (labeled-full-binary-tree-Magma X) M) → (X → type-Magma M)` pulling
back the label of `leaf-full-binary-tree` is an equivalence.

## Proof

This remains to be shown.
