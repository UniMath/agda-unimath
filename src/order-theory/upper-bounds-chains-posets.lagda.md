# Upper bounds of chains in posets

```agda
module order-theory.upper-bounds-chains-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.existential-quantification
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.propositions

open import order-theory.chains-posets
open import order-theory.posets
open import order-theory.upper-bounds-posets
```

</details>

## Idea

An **upper bound** of a chain `C` in a poset `P` is an element `x` such that for
every element `y` in `C`, `y ≤ x` holds.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (X : Poset l1 l2) (C : chain-Poset l3 X)
  where

  is-chain-upper-bound-Prop : type-Poset X → Prop (l1 ⊔ l2 ⊔ l3)
  is-chain-upper-bound-Prop =
    is-upper-bound-family-of-elements-Poset-Prop X
      ( inclusion-type-chain-Poset X C)

  is-chain-upper-bound : type-Poset X → UU (l1 ⊔ l2 ⊔ l3)
  is-chain-upper-bound = type-Prop ∘ is-chain-upper-bound-Prop

  has-chain-upper-bound-Prop : Prop (l1 ⊔ l2 ⊔ l3)
  has-chain-upper-bound-Prop = ∃ (type-Poset X) is-chain-upper-bound-Prop

  has-chain-upper-bound : UU (l1 ⊔ l2 ⊔ l3)
  has-chain-upper-bound = type-Prop has-chain-upper-bound-Prop
```
