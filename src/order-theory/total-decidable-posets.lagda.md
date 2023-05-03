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
open import order-theory.total-posets
```

</details>

## Definitions

```agda
total-decidable-Poset : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
total-decidable-Poset l1 l2 =
  Σ (Poset l1 l2) (λ X → is-total-Poset X × is-decidable-Poset X)

module _
  {l1 l2 : Level} (X : total-decidable-Poset l1 l2)
  where

  poset-total-decidable-Poset : Poset l1 l2
  poset-total-decidable-Poset = pr1 X

  is-total-poset-total-decidable-Poset :
    is-total-Poset (poset-total-decidable-Poset)
  is-total-poset-total-decidable-Poset = pr1 (pr2 X)

  is-decidable-poset-total-decidable-Poset :
    is-decidable-Poset (poset-total-decidable-Poset)
  is-decidable-poset-total-decidable-Poset = pr2 (pr2 X)

  element-total-decidable-Poset : UU l1
  element-total-decidable-Poset = element-Poset poset-total-decidable-Poset

  leq-total-decidable-poset-Prop :
    (x y : element-total-decidable-Poset) → Prop l2
  leq-total-decidable-poset-Prop = leq-poset-Prop poset-total-decidable-Poset

  leq-total-decidable-Poset :
    (x y : element-total-decidable-Poset) → UU l2
  leq-total-decidable-Poset = leq-Poset poset-total-decidable-Poset

  is-prop-leq-total-decidable-Poset :
    (x y : element-total-decidable-Poset) →
    is-prop (leq-total-decidable-Poset x y)
  is-prop-leq-total-decidable-Poset =
    is-prop-leq-Poset poset-total-decidable-Poset

  strict-leq-total-decidable-poset-Prop :
    (x y : element-total-decidable-Poset) → Prop (l1 ⊔ l2)
  strict-leq-total-decidable-poset-Prop =
    strict-leq-poset-Prop poset-total-decidable-Poset

  strict-leq-total-decidable-Poset :
    (x y : element-total-decidable-Poset) → UU (l1 ⊔ l2)
  strict-leq-total-decidable-Poset =
    strict-leq-Poset poset-total-decidable-Poset

  is-prop-strict-leq-total-decidable-Poset :
    (x y : element-total-decidable-Poset) →
    is-prop (strict-leq-total-decidable-Poset x y)
  is-prop-strict-leq-total-decidable-Poset =
    is-prop-strict-leq-Poset poset-total-decidable-Poset

  decidable-poset-total-decidable-Poset : decidable-Poset l1 l2
  pr1 decidable-poset-total-decidable-Poset = poset-total-decidable-Poset
  pr2 decidable-poset-total-decidable-Poset =
    is-decidable-poset-total-decidable-Poset

  leq-total-decidable-poset-decidable-Prop :
    (x y : element-total-decidable-Poset) → Decidable-Prop l2
  leq-total-decidable-poset-decidable-Prop =
    leq-decidable-poset-decidable-Prop decidable-poset-total-decidable-Poset

  concatenate-eq-leq-total-decidable-Poset :
    {x y z : element-total-decidable-Poset} → x ＝ y →
    leq-total-decidable-Poset y z → leq-total-decidable-Poset x z
  concatenate-eq-leq-total-decidable-Poset =
    concatenate-eq-leq-Poset poset-total-decidable-Poset

  concatenate-leq-eq-total-decidable-Poset :
    {x y z : element-total-decidable-Poset} →
    leq-total-decidable-Poset x y → y ＝ z → leq-total-decidable-Poset x z
  concatenate-leq-eq-total-decidable-Poset =
    concatenate-leq-eq-Poset poset-total-decidable-Poset

  refl-leq-total-decidable-Poset :
    (x : element-total-decidable-Poset) → leq-total-decidable-Poset x x
  refl-leq-total-decidable-Poset =
    refl-leq-Poset poset-total-decidable-Poset

  transitive-leq-total-decidable-Poset :
    (x y z : element-total-decidable-Poset) → leq-total-decidable-Poset y z →
    leq-total-decidable-Poset x y → leq-total-decidable-Poset x z
  transitive-leq-total-decidable-Poset =
    transitive-leq-Poset poset-total-decidable-Poset

  preorder-total-decidable-Poset : Preorder l1 l2
  preorder-total-decidable-Poset = preorder-Poset poset-total-decidable-Poset

  total-decidable-preorder-total-decidable-Poset :
    total-decidable-Preorder l1 l2
  pr1 total-decidable-preorder-total-decidable-Poset =
    preorder-total-decidable-Poset
  pr1 (pr2 total-decidable-preorder-total-decidable-Poset) =
    is-total-poset-total-decidable-Poset
  pr2 (pr2 total-decidable-preorder-total-decidable-Poset) =
    is-decidable-poset-total-decidable-Poset

  leq-or-strict-greater-decidable-Poset :
    (x y : element-total-decidable-Poset) → UU (l1 ⊔ l2)
  leq-or-strict-greater-decidable-Poset =
    leq-or-strict-greater-decidable-Preorder
      total-decidable-preorder-total-decidable-Poset

  is-leq-or-strict-greater-total-decidable-Poset :
    (x y : element-total-decidable-Poset) →
    leq-or-strict-greater-decidable-Poset x y
  is-leq-or-strict-greater-total-decidable-Poset =
    is-leq-or-strict-greater-total-decidable-Preorder
      total-decidable-preorder-total-decidable-Poset

  antisymmetric-leq-total-decidable-Poset :
    (x y : element-total-decidable-Poset) →
    leq-total-decidable-Poset x y → leq-total-decidable-Poset y x → Id x y
  antisymmetric-leq-total-decidable-Poset =
    antisymmetric-leq-Poset poset-total-decidable-Poset

  is-prop-leq-or-strict-greater-total-decidable-Poset :
    (x y : element-total-decidable-Poset) →
    is-prop (leq-or-strict-greater-decidable-Poset x y)
  is-prop-leq-or-strict-greater-total-decidable-Poset x y =
    is-prop-coprod
      ( λ p q →
        pr1 q (inv (antisymmetric-leq-total-decidable-Poset x y p (pr2 q))))
      ( is-prop-leq-total-decidable-Poset x y)
      ( is-prop-strict-leq-total-decidable-Poset y x)

  is-set-element-total-decidable-Poset : is-set element-total-decidable-Poset
  is-set-element-total-decidable-Poset =
    is-set-element-Poset poset-total-decidable-Poset

  element-total-decidable-poset-Set : Set l1
  element-total-decidable-poset-Set =
    element-poset-Set poset-total-decidable-Poset
```
