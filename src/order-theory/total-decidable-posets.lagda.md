# Totally ordered decidable posets

```agda
module order-theory.total-decidable-posets where
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
open import order-theory.posets
open import order-theory.preorders
open import order-theory.total-decidable-preorders
open import order-theory.total-orders
```

</details>

## Definitions

```agda
total-Decidable-Poset : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
total-Decidable-Poset l1 l2 =
  Σ (Poset l1 l2) (λ X → is-total-Poset X × is-decidable-Poset X)

module _
  {l1 l2 : Level} (X : total-Decidable-Poset l1 l2)
  where

  poset-total-Decidable-Poset : Poset l1 l2
  poset-total-Decidable-Poset = pr1 X

  is-total-poset-total-Decidable-Poset :
    is-total-Poset (poset-total-Decidable-Poset)
  is-total-poset-total-Decidable-Poset = pr1 (pr2 X)

  is-decidable-poset-total-Decidable-Poset :
    is-decidable-Poset (poset-total-Decidable-Poset)
  is-decidable-poset-total-Decidable-Poset = pr2 (pr2 X)

  element-total-Decidable-Poset : UU l1
  element-total-Decidable-Poset = element-Poset poset-total-Decidable-Poset

  leq-total-Decidable-Poset-Prop :
    (x y : element-total-Decidable-Poset) → Prop l2
  leq-total-Decidable-Poset-Prop = leq-Poset-Prop poset-total-Decidable-Poset

  leq-total-Decidable-Poset :
    (x y : element-total-Decidable-Poset) → UU l2
  leq-total-Decidable-Poset = leq-Poset poset-total-Decidable-Poset

  is-prop-leq-total-Decidable-Poset :
    (x y : element-total-Decidable-Poset) →
    is-prop (leq-total-Decidable-Poset x y)
  is-prop-leq-total-Decidable-Poset =
    is-prop-leq-Poset poset-total-Decidable-Poset

  strict-leq-total-Decidable-Poset-Prop :
    (x y : element-total-Decidable-Poset) → Prop (l1 ⊔ l2)
  strict-leq-total-Decidable-Poset-Prop =
    strict-leq-Poset-Prop poset-total-Decidable-Poset

  strict-leq-total-Decidable-Poset :
    (x y : element-total-Decidable-Poset) → UU (l1 ⊔ l2)
  strict-leq-total-Decidable-Poset =
    strict-leq-Poset poset-total-Decidable-Poset

  is-prop-strict-leq-total-Decidable-Poset :
    (x y : element-total-Decidable-Poset) →
    is-prop (strict-leq-total-Decidable-Poset x y)
  is-prop-strict-leq-total-Decidable-Poset =
    is-prop-strict-leq-Poset poset-total-Decidable-Poset

  decidable-poset-total-Decidable-Poset : Decidable-Poset l1 l2
  pr1 decidable-poset-total-Decidable-Poset = poset-total-Decidable-Poset
  pr2 decidable-poset-total-Decidable-Poset =
    is-decidable-poset-total-Decidable-Poset

  leq-total-decidable-poset-decidable-Prop :
    (x y : element-total-Decidable-Poset) → Decidable-Prop l2
  leq-total-decidable-poset-decidable-Prop =
    leq-decidable-poset-decidable-Prop decidable-poset-total-Decidable-Poset

  concatenate-eq-leq-total-Decidable-Poset :
    {x y z : element-total-Decidable-Poset} → x ＝ y →
    leq-total-Decidable-Poset y z → leq-total-Decidable-Poset x z
  concatenate-eq-leq-total-Decidable-Poset =
    concatenate-eq-leq-Poset poset-total-Decidable-Poset

  concatenate-leq-eq-total-Decidable-Poset :
    {x y z : element-total-Decidable-Poset} →
    leq-total-Decidable-Poset x y → y ＝ z → leq-total-Decidable-Poset x z
  concatenate-leq-eq-total-Decidable-Poset =
    concatenate-leq-eq-Poset poset-total-Decidable-Poset

  refl-leq-total-Decidable-Poset :
    (x : element-total-Decidable-Poset) → leq-total-Decidable-Poset x x
  refl-leq-total-Decidable-Poset =
    refl-leq-Poset poset-total-Decidable-Poset

  transitive-leq-total-Decidable-Poset :
    (x y z : element-total-Decidable-Poset) → leq-total-Decidable-Poset y z →
    leq-total-Decidable-Poset x y → leq-total-Decidable-Poset x z
  transitive-leq-total-Decidable-Poset =
    transitive-leq-Poset poset-total-Decidable-Poset

  preorder-total-Decidable-Poset : Preorder l1 l2
  preorder-total-Decidable-Poset = preorder-Poset poset-total-Decidable-Poset

  total-decidable-preorder-total-Decidable-Poset :
    total-decidable-Preorder l1 l2
  pr1 total-decidable-preorder-total-Decidable-Poset =
    preorder-total-Decidable-Poset
  pr1 (pr2 total-decidable-preorder-total-Decidable-Poset) =
    is-total-poset-total-Decidable-Poset
  pr2 (pr2 total-decidable-preorder-total-Decidable-Poset) =
    is-decidable-poset-total-Decidable-Poset

  leq-or-strict-greater-Decidable-Poset :
    (x y : element-total-Decidable-Poset) → UU (l1 ⊔ l2)
  leq-or-strict-greater-Decidable-Poset =
    leq-or-strict-greater-decidable-Preorder
      total-decidable-preorder-total-Decidable-Poset

  is-leq-or-strict-greater-total-Decidable-Poset :
    (x y : element-total-Decidable-Poset) →
    leq-or-strict-greater-Decidable-Poset x y
  is-leq-or-strict-greater-total-Decidable-Poset =
    is-leq-or-strict-greater-total-decidable-Preorder
      total-decidable-preorder-total-Decidable-Poset

  antisymmetric-leq-total-Decidable-Poset :
    (x y : element-total-Decidable-Poset) →
    leq-total-Decidable-Poset x y → leq-total-Decidable-Poset y x → Id x y
  antisymmetric-leq-total-Decidable-Poset =
    antisymmetric-leq-Poset poset-total-Decidable-Poset

  is-prop-leq-or-strict-greater-total-Decidable-Poset :
    (x y : element-total-Decidable-Poset) →
    is-prop (leq-or-strict-greater-Decidable-Poset x y)
  is-prop-leq-or-strict-greater-total-Decidable-Poset x y =
    is-prop-coprod
      ( λ p q →
        pr1 q (inv (antisymmetric-leq-total-Decidable-Poset x y p (pr2 q))))
      ( is-prop-leq-total-Decidable-Poset x y)
      ( is-prop-strict-leq-total-Decidable-Poset y x)

  is-set-element-total-Decidable-Poset : is-set element-total-Decidable-Poset
  is-set-element-total-Decidable-Poset =
    is-set-element-Poset poset-total-Decidable-Poset

  element-total-decidable-poset-Set : Set l1
  element-total-decidable-poset-Set =
    element-poset-Set poset-total-Decidable-Poset
```
