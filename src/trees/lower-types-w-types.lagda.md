# Lower types of elements in W-types

```agda
module trees.lower-types-w-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.existential-quantification
open import foundation.universe-levels

open import trees.ranks-of-elements-w-types
open import trees.w-types
```

</details>

## Idea

We define by induction a type family over `W A B` in a way that generalizes the
construction of the standard finite types over ℕ to arbitrary W-types.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  data
    lower-𝕎 : 𝕎 A B → UU (l1 ⊔ l2)
    where
    lower-tree-𝕎 :
      {x : A} {f : B x → 𝕎 A B} →
      ((y : B x) → lower-𝕎 (f y)) → lower-𝕎 (tree-𝕎 x f)

  inclusion-lower-𝕎 : {x : 𝕎 A B} → lower-𝕎 x → 𝕎 A B
  inclusion-lower-𝕎 (lower-tree-𝕎 {a} {f} g) =
    tree-𝕎 a (λ y → inclusion-lower-𝕎 (g y))

  upper-bound-rank-inclusion-lower-𝕎 :
    {x : 𝕎 A B} (y : lower-𝕎 x) → inclusion-lower-𝕎 y ≼-𝕎 x
  upper-bound-rank-inclusion-lower-𝕎 (lower-tree-𝕎 g) y =
    intro-exists y (upper-bound-rank-inclusion-lower-𝕎 (g y))
```
