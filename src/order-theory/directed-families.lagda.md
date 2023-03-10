# Directed families in posets

```agda
module order-theory.directed-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.existential-quantification
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.posets
```

</details>

## Definition

```agda
is-directed-family-poset-Prop :
  {l1 l2 l3 : Level} (P : Poset l1 l2) (I : Inhabited-Type l3)
  (α : type-Inhabited-Type I → element-Poset P) → Prop (l2 ⊔ l3)
is-directed-family-poset-Prop P I α =
  Π-Prop
    ( type-Inhabited-Type I)
    ( λ i →
      Π-Prop
        ( type-Inhabited-Type I)
        ( λ j →
          ∃-Prop (type-Inhabited-Type I) (λ k → leq-Poset P (α i) (α k) × leq-Poset P (α j) (α k))))

is-directed-family-Poset :
  {l1 l2 l3 : Level} (P : Poset l1 l2) (I : Inhabited-Type l3)
  (α : type-Inhabited-Type I → element-Poset P) → UU (l2 ⊔ l3)
is-directed-family-Poset P I α = type-Prop (is-directed-family-poset-Prop P I α)
```
