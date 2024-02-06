# Cartesian product types

```agda
module foundation-core.cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Definition

Cartesian products of types are defined as dependent pair types, using a
constant type family.

```agda
product : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
product A B = Σ A (λ _ → B)

pair' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → A → B → product A B
pair' = pair

infixr 15 _×_
_×_ : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
_×_ = product
```
