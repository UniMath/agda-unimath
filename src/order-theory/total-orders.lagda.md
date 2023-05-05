# Total orders

```agda
module order-theory.total-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.preorders
open import order-theory.total-preorders
```

</details>

## Definitions

### Being a totally ordered poset

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  incident-Poset-Prop : (x y : element-Poset X) → Prop l2
  incident-Poset-Prop = incident-Preorder-Prop (preorder-Poset X)

  incident-Poset : (x y : element-Poset X) → UU l2
  incident-Poset = incident-Preorder (preorder-Poset X)

  is-prop-incident-Poset :
    (x y : element-Poset X) → is-prop (incident-Poset x y)
  is-prop-incident-Poset = is-prop-incident-Preorder (preorder-Poset X)

  is-total-Poset-Prop : Prop (l1 ⊔ l2)
  is-total-Poset-Prop = is-total-Preorder-Prop (preorder-Poset X)

  is-total-Poset : UU (l1 ⊔ l2)
  is-total-Poset = is-total-Preorder (preorder-Poset X)

  is-prop-is-total-Poset : is-prop is-total-Poset
  is-prop-is-total-Poset = is-prop-is-total-Preorder (preorder-Poset X)
```

### Type of total posets

```agda
Total-Order : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Total-Order l1 l2 = Σ (Poset l1 l2) is-total-Poset

module _
  {l1 l2 : Level} (X : Total-Order l1 l2)
  where

  poset-Total-Order : Poset l1 l2
  poset-Total-Order = pr1 X

  preorder-Total-Order : Preorder l1 l2
  preorder-Total-Order = preorder-Poset poset-Total-Order

  is-total-Total-Order : is-total-Poset (poset-Total-Order)
  is-total-Total-Order = pr2 X

  element-Total-Order : UU l1
  element-Total-Order = element-Poset poset-Total-Order

  leq-Total-Order-Prop : (x y : element-Total-Order) → Prop l2
  leq-Total-Order-Prop = leq-Poset-Prop poset-Total-Order

  leq-Total-Order : (x y : element-Total-Order) → UU l2
  leq-Total-Order = leq-Poset poset-Total-Order

  is-prop-leq-Total-Order :
    (x y : element-Total-Order) → is-prop (leq-Total-Order x y)
  is-prop-leq-Total-Order = is-prop-leq-Poset poset-Total-Order

  concatenate-eq-leq-Total-Order :
    {x y z : element-Total-Order} → x ＝ y →
    leq-Total-Order y z → leq-Total-Order x z
  concatenate-eq-leq-Total-Order = concatenate-eq-leq-Poset poset-Total-Order

  concatenate-leq-eq-Total-Order :
    {x y z : element-Total-Order} →
    leq-Total-Order x y → y ＝ z → leq-Total-Order x z
  concatenate-leq-eq-Total-Order = concatenate-leq-eq-Poset poset-Total-Order

  refl-leq-Total-Order : (x : element-Total-Order) → leq-Total-Order x x
  refl-leq-Total-Order = refl-leq-Poset poset-Total-Order

  transitive-leq-Total-Order :
    (x y z : element-Total-Order) → leq-Total-Order y z →
    leq-Total-Order x y → leq-Total-Order x z
  transitive-leq-Total-Order = transitive-leq-Poset poset-Total-Order

  antisymmetric-leq-Total-Order :
    (x y : element-Total-Order) →
    leq-Total-Order x y → leq-Total-Order y x → Id x y
  antisymmetric-leq-Total-Order = antisymmetric-leq-Poset poset-Total-Order

  is-set-element-Total-Order : is-set element-Total-Order
  is-set-element-Total-Order = is-set-element-Poset poset-Total-Order

  set-Total-Order : Set l1
  set-Total-Order = set-Poset poset-Total-Order
```
