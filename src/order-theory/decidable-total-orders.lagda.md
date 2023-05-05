# Decidable total orders

```agda
module order-theory.decidable-total-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.decidable-posets
open import order-theory.decidable-total-preorders
open import order-theory.posets
open import order-theory.preorders
open import order-theory.total-orders
```

</details>

## Definitions

```agda
Decidable-Total-Order : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Decidable-Total-Order l1 l2 =
  Σ (Poset l1 l2) (λ P → is-total-Poset P × is-decidable-leq-Poset P)

module _
  {l1 l2 : Level} (P : Decidable-Total-Order l1 l2)
  where

  poset-Decidable-Total-Order : Poset l1 l2
  poset-Decidable-Total-Order = pr1 P

  is-total-poset-Decidable-Total-Order :
    is-total-Poset (poset-Decidable-Total-Order)
  is-total-poset-Decidable-Total-Order = pr1 (pr2 P)

  is-decidable-poset-Decidable-Total-Order :
    is-decidable-leq-Poset (poset-Decidable-Total-Order)
  is-decidable-poset-Decidable-Total-Order = pr2 (pr2 P)

  element-Decidable-Total-Order : UU l1
  element-Decidable-Total-Order = element-Poset poset-Decidable-Total-Order

  leq-Decidable-Total-Order-Prop :
    (x y : element-Decidable-Total-Order) → Prop l2
  leq-Decidable-Total-Order-Prop = leq-Poset-Prop poset-Decidable-Total-Order

  leq-Decidable-Total-Order :
    (x y : element-Decidable-Total-Order) → UU l2
  leq-Decidable-Total-Order = leq-Poset poset-Decidable-Total-Order

  is-prop-leq-Decidable-Total-Order :
    (x y : element-Decidable-Total-Order) →
    is-prop (leq-Decidable-Total-Order x y)
  is-prop-leq-Decidable-Total-Order =
    is-prop-leq-Poset poset-Decidable-Total-Order

  le-Decidable-Total-Order-Prop :
    (x y : element-Decidable-Total-Order) → Prop (l1 ⊔ l2)
  le-Decidable-Total-Order-Prop =
    le-Poset-Prop poset-Decidable-Total-Order

  le-Decidable-Total-Order :
    (x y : element-Decidable-Total-Order) → UU (l1 ⊔ l2)
  le-Decidable-Total-Order =
    le-Poset poset-Decidable-Total-Order

  is-prop-le-Decidable-Total-Order :
    (x y : element-Decidable-Total-Order) →
    is-prop (le-Decidable-Total-Order x y)
  is-prop-le-Decidable-Total-Order =
    is-prop-le-Poset poset-Decidable-Total-Order

  decidable-poset-Decidable-Total-Order : Decidable-Poset l1 l2
  pr1 decidable-poset-Decidable-Total-Order = poset-Decidable-Total-Order
  pr2 decidable-poset-Decidable-Total-Order =
    is-decidable-poset-Decidable-Total-Order

  leq-total-decidable-poset-decidable-Prop :
    (x y : element-Decidable-Total-Order) → Decidable-Prop l2
  leq-total-decidable-poset-decidable-Prop =
    leq-decidable-poset-decidable-Prop decidable-poset-Decidable-Total-Order

  concatenate-eq-leq-Decidable-Total-Order :
    {x y z : element-Decidable-Total-Order} → x ＝ y →
    leq-Decidable-Total-Order y z → leq-Decidable-Total-Order x z
  concatenate-eq-leq-Decidable-Total-Order =
    concatenate-eq-leq-Poset poset-Decidable-Total-Order

  concatenate-leq-eq-Decidable-Total-Order :
    {x y z : element-Decidable-Total-Order} →
    leq-Decidable-Total-Order x y → y ＝ z → leq-Decidable-Total-Order x z
  concatenate-leq-eq-Decidable-Total-Order =
    concatenate-leq-eq-Poset poset-Decidable-Total-Order

  refl-leq-Decidable-Total-Order :
    (x : element-Decidable-Total-Order) → leq-Decidable-Total-Order x x
  refl-leq-Decidable-Total-Order =
    refl-leq-Poset poset-Decidable-Total-Order

  transitive-leq-Decidable-Total-Order :
    (x y z : element-Decidable-Total-Order) → leq-Decidable-Total-Order y z →
    leq-Decidable-Total-Order x y → leq-Decidable-Total-Order x z
  transitive-leq-Decidable-Total-Order =
    transitive-leq-Poset poset-Decidable-Total-Order

  preorder-Decidable-Total-Order : Preorder l1 l2
  preorder-Decidable-Total-Order = preorder-Poset poset-Decidable-Total-Order

  decidable-total-preorder-Decidable-Total-Order :
    Decidable-Total-Preorder l1 l2
  pr1 decidable-total-preorder-Decidable-Total-Order =
    preorder-Decidable-Total-Order
  pr1 (pr2 decidable-total-preorder-Decidable-Total-Order) =
    is-total-poset-Decidable-Total-Order
  pr2 (pr2 decidable-total-preorder-Decidable-Total-Order) =
    is-decidable-poset-Decidable-Total-Order

  leq-or-strict-greater-Decidable-Poset :
    (x y : element-Decidable-Total-Order) → UU (l1 ⊔ l2)
  leq-or-strict-greater-Decidable-Poset =
    leq-or-strict-greater-Decidable-Preorder
      decidable-total-preorder-Decidable-Total-Order

  is-leq-or-strict-greater-Decidable-Total-Order :
    (x y : element-Decidable-Total-Order) →
    leq-or-strict-greater-Decidable-Poset x y
  is-leq-or-strict-greater-Decidable-Total-Order =
    is-leq-or-strict-greater-Decidable-Total-Preorder
      decidable-total-preorder-Decidable-Total-Order

  antisymmetric-leq-Decidable-Total-Order :
    (x y : element-Decidable-Total-Order) →
    leq-Decidable-Total-Order x y → leq-Decidable-Total-Order y x → Id x y
  antisymmetric-leq-Decidable-Total-Order =
    antisymmetric-leq-Poset poset-Decidable-Total-Order

  is-prop-leq-or-strict-greater-Decidable-Total-Order :
    (x y : element-Decidable-Total-Order) →
    is-prop (leq-or-strict-greater-Decidable-Poset x y)
  is-prop-leq-or-strict-greater-Decidable-Total-Order x y =
    is-prop-coprod
      ( λ p q →
        pr1 q (inv (antisymmetric-leq-Decidable-Total-Order x y p (pr2 q))))
      ( is-prop-leq-Decidable-Total-Order x y)
      ( is-prop-le-Decidable-Total-Order y x)

  is-set-element-Decidable-Total-Order : is-set element-Decidable-Total-Order
  is-set-element-Decidable-Total-Order =
    is-set-element-Poset poset-Decidable-Total-Order

  set-Decidable-Total-Order : Set l1
  set-Decidable-Total-Order = set-Poset poset-Decidable-Total-Order
```
