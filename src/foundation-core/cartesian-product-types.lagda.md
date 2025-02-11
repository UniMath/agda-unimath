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

## Definitions

Cartesian products of types are defined as dependent pair types, using a
constant type family.

### The cartesian product type

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

### The induction principle for the cartesian product type

```agda
ind-product :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A × B → UU l3} →
  ((x : A) (y : B) → C (x , y)) → (t : A × B) → C t
ind-product = ind-Σ
```

### The recursion principle for the cartesian product type

```agda
rec-product :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (A → B → C) → (A × B) → C
rec-product = ind-product
```
