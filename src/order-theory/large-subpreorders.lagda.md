# Large subpreorders

```agda
module order-theory.large-subpreorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-preorders
```

</details>

## Idea

A **large subpreorder** of a [large preorder](order-theory.large-preorders.md)
`P` consists of a subtype

```text
  S : type-Large-Preorder P l → Prop (γ l)
```

for each universe level `l`, where `γ : Level → Level` is a universe level
reindexing function.

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

  is-in-Large-Subpreorder :
    {l1 : Level} → type-Large-Preorder P l1 → UU (γ l1)
  is-in-Large-Subpreorder {l1} = is-in-subtype (S {l1})

  is-prop-is-in-Large-Subpreorder :
    {l1 : Level} (x : type-Large-Preorder P l1) →
    is-prop (is-in-Large-Subpreorder x)
  is-prop-is-in-Large-Subpreorder {l1} =
    is-prop-is-in-subtype (S {l1})

  type-Large-Subpreorder : (l1 : Level) → UU (α l1 ⊔ γ l1)
  type-Large-Subpreorder l1 = type-subtype (S {l1})

  leq-Large-Subpreorder-Prop :
    Large-Relation-Prop (λ l → α l ⊔ γ l) β type-Large-Subpreorder
  leq-Large-Subpreorder-Prop x y =
    leq-Large-Preorder-Prop P (pr1 x) (pr1 y)

  leq-Large-Subpreorder :
    Large-Relation (λ l → α l ⊔ γ l) β type-Large-Subpreorder
  leq-Large-Subpreorder x y = type-Prop (leq-Large-Subpreorder-Prop x y)

  is-prop-leq-Large-Subpreorder :
    is-prop-Large-Relation type-Large-Subpreorder leq-Large-Subpreorder
  is-prop-leq-Large-Subpreorder x y =
    is-prop-type-Prop (leq-Large-Subpreorder-Prop x y)

  refl-leq-Large-Subpreorder :
    is-large-reflexive type-Large-Subpreorder leq-Large-Subpreorder
  refl-leq-Large-Subpreorder (x , p) = refl-leq-Large-Preorder P x

  transitive-leq-Large-Subpreorder :
    is-large-transitive type-Large-Subpreorder leq-Large-Subpreorder
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
