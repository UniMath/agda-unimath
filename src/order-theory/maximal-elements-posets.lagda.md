# Maximal elements in posets

```agda
module order-theory.maximal-elements-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.posets
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-maximal-element-Poset-Prop : type-Poset X → Prop (l1 ⊔ l2)
  is-maximal-element-Poset-Prop x =
    Π-Prop
      ( type-Poset X)
      ( λ y → function-Prop (leq-Poset X x y) (y ＝ x , is-set-type-Poset X y x))

  is-maximal-element-Poset : type-Poset X → UU (l1 ⊔ l2)
  is-maximal-element-Poset x = type-Prop (is-maximal-element-Poset-Prop x)

  is-prop-is-maximal-element-Poset :
    (x : type-Poset X) → is-prop (is-maximal-element-Poset x)
  is-prop-is-maximal-element-Poset x =
    is-prop-type-Prop (is-maximal-element-Poset-Prop x)

  has-maximal-element-Poset : UU (l1 ⊔ l2)
  has-maximal-element-Poset = Σ (type-Poset X) is-maximal-element-Poset
```
