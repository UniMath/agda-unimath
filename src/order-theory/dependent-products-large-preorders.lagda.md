# Dependent products large preorders

```agda
module order-theory.dependent-products-large-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.large-preorders
```

</details>

## Idea

Given a family `P : I → Large-Preorder α β` of large preorders indexed by a type
`I : UU l`, the dependent prodcut of the large preorders `P i` is again a large
preorder.

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {l : Level} {I : UU l} (P : I → Large-Preorder α β)
  where

  type-Π-Large-Preorder : (l1 : Level) → UU (α l1 ⊔ l)
  type-Π-Large-Preorder l1 = (i : I) → type-Large-Preorder (P i) l1

  leq-Π-Large-Preorder-Prop :
    {l1 l2 : Level} →
    type-Π-Large-Preorder l1 → type-Π-Large-Preorder l2 → Prop (β l1 l2 ⊔ l)
  leq-Π-Large-Preorder-Prop x y =
    Π-Prop I (λ i → leq-Large-Preorder-Prop (P i) (x i) (y i))

  leq-Π-Large-Preorder :
    {l1 l2 : Level} →
    type-Π-Large-Preorder l1 → type-Π-Large-Preorder l2 → UU (β l1 l2 ⊔ l)
  leq-Π-Large-Preorder x y =
    type-Prop (leq-Π-Large-Preorder-Prop x y)

  is-prop-leq-Π-Large-Preorder :
    {l1 l2 : Level}
    (x : type-Π-Large-Preorder l1) (y : type-Π-Large-Preorder l2) →
    is-prop (leq-Π-Large-Preorder x y)
  is-prop-leq-Π-Large-Preorder x y =
    is-prop-type-Prop (leq-Π-Large-Preorder-Prop x y)

  refl-leq-Π-Large-Preorder :
    {l1 : Level} → is-reflexive (leq-Π-Large-Preorder {l1})
  refl-leq-Π-Large-Preorder x i = refl-leq-Large-Preorder (P i) (x i)

  transitive-leq-Π-Large-Preorder :
    {l1 l2 l3 : Level}
    (x : type-Π-Large-Preorder l1)
    (y : type-Π-Large-Preorder l2)
    (z : type-Π-Large-Preorder l3) →
    leq-Π-Large-Preorder y z →
    leq-Π-Large-Preorder x y →
    leq-Π-Large-Preorder x z
  transitive-leq-Π-Large-Preorder x y z H K i =
    transitive-leq-Large-Preorder (P i) (x i) (y i) (z i) (H i) (K i)

  Π-Large-Preorder : Large-Preorder (λ l1 → α l1 ⊔ l) (λ l1 l2 → β l1 l2 ⊔ l)
  type-Large-Preorder Π-Large-Preorder =
    type-Π-Large-Preorder
  leq-Large-Preorder-Prop Π-Large-Preorder =
    leq-Π-Large-Preorder-Prop
  refl-leq-Large-Preorder Π-Large-Preorder =
    refl-leq-Π-Large-Preorder
  transitive-leq-Large-Preorder Π-Large-Preorder =
    transitive-leq-Π-Large-Preorder
```
