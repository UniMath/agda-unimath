# Cartesian product types

```agda
{-# OPTIONS --safe #-}
```

```agda
module foundation-core.cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.dependent-pair-types
open import foundation-core.universe-levels
```

</details>

## Definition

Cartesian products of types are defined as dependent pair types, using a constant type family.

```agda
prod : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
prod A B = Σ A (λ a → B)

pair' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → A → B → prod A B
pair' = pair

_×_ :  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
A × B = prod A B
```
