# Totally ordered posets

```agda
module order-theory.total-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.total-preorders
```

</details>

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  incident-poset-Prop : (x y : element-Poset X) → Prop l2
  incident-poset-Prop = incident-preorder-Prop (preorder-Poset X)

  incident-Poset : (x y : element-Poset X) → UU l2
  incident-Poset = incident-Preorder (preorder-Poset X)

  is-prop-incident-Poset :
    (x y : element-Poset X) → is-prop (incident-Poset x y)
  is-prop-incident-Poset = is-prop-incident-Preorder (preorder-Poset X)

  is-total-poset-Prop : Prop (l1 ⊔ l2)
  is-total-poset-Prop = is-total-preorder-Prop (preorder-Poset X)

  is-total-Poset : UU (l1 ⊔ l2)
  is-total-Poset = is-total-Preorder (preorder-Poset X)

  is-prop-is-total-Poset : is-prop is-total-Poset
  is-prop-is-total-Poset = is-prop-is-total-Preorder (preorder-Poset X)
```
