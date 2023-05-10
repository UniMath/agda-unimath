# Large subpreorders

```agda
module order-theory.large-subpreorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-preorders
```

</details>

## Idea

A **large subpreorder** of a [large preorder](order-theory.large-preorders.md) `P` consists of a subtype

```md
  S : type-Large-Preorder P l → Prop (γ l)
```

for each universe level `l`, where `γ : Level → Level` is a universe level reindexing function.

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (γ : Level → Level)
  (P : Large-Preorder α β)
  where

  Large-Subpreorder : UUω
  Large-Subpreorder = {l : Level} → type-Large-Preorder P l → Prop (γ l)

module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level → Level}
  (P : Large-Preorder α β) (S : Large-Subpreorder γ P)
  where

  type-Large-Subpreorder : (l1 : Level) → UU (α l1 ⊔ γ l1)
  type-Large-Subpreorder l1 = type-subtype (S {l1})

  leq-Large-Subpreorder-Prop :
    {l1 l2 : Level} →
    type-Large-Subpreorder l1 → type-Large-Subpreorder l2 → Prop (β l1 l2)
  leq-Large-Subpreorder-Prop (x , p) (y , q) = leq-Large-Preorder-Prop P x y

  leq-Large-Subpreorder :
    {l1 l2 : Level} →
    type-Large-Subpreorder l1 → type-Large-Subpreorder l2 → UU (β l1 l2)
  leq-Large-Subpreorder x y = type-Prop (leq-Large-Subpreorder-Prop x y)

  is-prop-leq-Large-Subpreorder :
    {l1 l2 : Level} →
    (x : type-Large-Subpreorder l1) (y : type-Large-Subpreorder l2) →
    is-prop (leq-Large-Subpreorder x y)
  is-prop-leq-Large-Subpreorder x y =
    is-prop-type-Prop (leq-Large-Subpreorder-Prop x y)

  refl-leq-Large-Subpreorder :
    {l1 : Level} (x : type-Large-Subpreorder l1) →
    leq-Large-Subpreorder x x
  refl-leq-Large-Subpreorder (x , p) = refl-leq-Large-Preorder P x

  transitive-leq-Large-Subpreorder :
    {l1 l2 l3 : Level}
    (x : type-Large-Subpreorder l1)
    (y : type-Large-Subpreorder l2)
    (z : type-Large-Subpreorder l3) →
    leq-Large-Subpreorder y z → leq-Large-Subpreorder x y →
    leq-Large-Subpreorder x z
  transitive-leq-Large-Subpreorder (x , p) (y , q) (z , r) =
    transitive-leq-Large-Preorder P x y z

  large-preorder-Large-Subpreorder :
    Large-Preorder (λ l → α l ⊔ γ l) (λ l1 l2 → β l1 l2)
  type-Large-Preorder
    large-preorder-Large-Subpreorder =
    type-Large-Subpreorder
  leq-Large-Preorder-Prop
    large-preorder-Large-Subpreorder =
    leq-Large-Subpreorder-Prop
  refl-leq-Large-Preorder
    large-preorder-Large-Subpreorder =
    refl-leq-Large-Subpreorder
  transitive-leq-Large-Preorder
    large-preorder-Large-Subpreorder =
    transitive-leq-Large-Subpreorder
```
