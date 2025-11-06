# The elementhood relation on W-types

```agda
module trees.elementhood-relation-w-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import trees.elementhood-relation-coalgebras-polynomial-endofunctors
open import trees.w-types
```

</details>

## Idea

We say that a [tree](trees.w-types.md) `S` is an
{{#concept "element" Disambiguation="W-types" Agda=_∈-𝕎_}} of a tree
`tree-𝕎 x α` if `S` can be equipped with an element `y : B x` such that
`α y = S`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  infix 6 _∈-𝕎_ _∉-𝕎_

  _∈-𝕎_ : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  x ∈-𝕎 y = x ∈ y in-coalgebra 𝕎-Coalg A B

  _∉-𝕎_ : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  x ∉-𝕎 y = is-empty (x ∈-𝕎 y)
```

## Properties

```agda
irreflexive-∈-𝕎 :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (x : 𝕎 A B) → x ∉-𝕎 x
irreflexive-∈-𝕎 {A = A} {B = B} (tree-𝕎 x α) (pair y p) =
  irreflexive-∈-𝕎 (α y) (tr (λ z → (α y) ∈-𝕎 z) (inv p) (pair y refl))
```
