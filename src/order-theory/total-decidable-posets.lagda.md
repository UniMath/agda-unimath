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
  {l1 l2  : Level} (X : total-decidable-Poset l1 l2)
  where

  Poset-total-decidable-Poset : Poset l1 l2
  Poset-total-decidable-Poset = pr1 X

  is-total-Poset-total-decidable-Poset :
    is-total-Poset (Poset-total-decidable-Poset)
  is-total-Poset-total-decidable-Poset = pr1 (pr2 X)

  is-decidable-Poset-total-decidable-Poset :
    is-decidable-Poset (Poset-total-decidable-Poset)
  is-decidable-Poset-total-decidable-Poset = pr2 (pr2 X)

  element-total-decidable-Poset : UU l1
  element-total-decidable-Poset = pr1 Poset-total-decidable-Poset

  leq-total-decidable-poset-Prop :
    (x y : element-total-decidable-Poset) → Prop l2
  leq-total-decidable-poset-Prop = pr1 (pr2 Poset-total-decidable-Poset)

  leq-total-decidable-Poset :
    (x y : element-total-decidable-Poset) → UU l2
  leq-total-decidable-Poset x y = type-Prop (leq-total-decidable-poset-Prop x y)

  is-prop-leq-total-decidable-Poset :
    (x y : element-total-decidable-Poset) →
    is-prop (leq-total-decidable-Poset x y)
  is-prop-leq-total-decidable-Poset x y =
    is-prop-type-Prop (leq-total-decidable-poset-Prop x y)

  is-decidable-leq-total-decidable-Poset :
    (x y : element-total-decidable-Poset) →
    is-decidable (leq-total-decidable-Poset x y)
  is-decidable-leq-total-decidable-Poset =
    is-decidable-Poset-total-decidable-Poset

  leq-total-decidable-poset-decidable-Prop :
    (x y : element-total-decidable-Poset) → decidable-Prop l2
  pr1 (leq-total-decidable-poset-decidable-Prop x y) =
    leq-total-decidable-Poset x y
  pr1 (pr2 (leq-total-decidable-poset-decidable-Prop x y)) =
    is-prop-leq-total-decidable-Poset x y
  pr2 (pr2 (leq-total-decidable-poset-decidable-Prop x y)) =
    is-decidable-leq-total-decidable-Poset x y

  concatenate-eq-leq-total-decidable-Poset :
    {x y z : element-total-decidable-Poset} → x ＝ y →
    leq-total-decidable-Poset y z → leq-total-decidable-Poset x z
  concatenate-eq-leq-total-decidable-Poset refl H = H

  concatenate-leq-eq-total-decidable-Poset :
    {x y z : element-total-decidable-Poset} →
    leq-total-decidable-Poset x y → y ＝ z → leq-total-decidable-Poset x z
  concatenate-leq-eq-total-decidable-Poset H refl = H

  refl-leq-total-decidable-Poset :
    (x : element-total-decidable-Poset) → leq-total-decidable-Poset x x
  refl-leq-total-decidable-Poset =
    pr1 (pr1 (pr2 (pr2 Poset-total-decidable-Poset)))

  transitive-leq-total-decidable-Poset :
    (x y z : element-total-decidable-Poset) → leq-total-decidable-Poset y z →
    leq-total-decidable-Poset x y → leq-total-decidable-Poset x z
  transitive-leq-total-decidable-Poset =
    pr2 (pr1 (pr2 (pr2 Poset-total-decidable-Poset)))

  preorder-total-decidable-Poset : Preorder l1 l2
  pr1 preorder-total-decidable-Poset = element-total-decidable-Poset
  pr1 (pr2 preorder-total-decidable-Poset) = leq-total-decidable-poset-Prop
  pr1 (pr2 (pr2 preorder-total-decidable-Poset)) = refl-leq-total-decidable-Poset
  pr2 (pr2 (pr2 preorder-total-decidable-Poset)) =
    transitive-leq-total-decidable-Poset

  total-decidable-preorder-total-decidable-Poset : total-decidable-Preorder l1 l2
  pr1 total-decidable-preorder-total-decidable-Poset =
    preorder-total-decidable-Poset
  pr1 (pr2 total-decidable-preorder-total-decidable-Poset) =
    is-total-Poset-total-decidable-Poset
  pr2 (pr2 total-decidable-preorder-total-decidable-Poset) =
    is-decidable-Poset-total-decidable-Poset

  leq-or-strict-greater-decidable-Poset :
    (x y : element-total-decidable-Poset) → UU (l1 ⊔ l2)
  leq-or-strict-greater-decidable-Poset x y =
    leq-or-strict-greater-decidable-Preorder
      total-decidable-preorder-total-decidable-Poset
      x
      y

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
    pr2 (pr2 (pr2 Poset-total-decidable-Poset))

  is-prop-leq-or-strict-greater-total-decidable-Poset :
    (x y : element-total-decidable-Poset) →
    is-prop (leq-or-strict-greater-decidable-Poset x y)
  is-prop-leq-or-strict-greater-total-decidable-Poset x y =
    is-prop-coprod
      ( λ p q →
        pr1 q (antisymmetric-leq-total-decidable-Poset x y p (pr2 q) ))
      ( is-prop-leq-total-decidable-Poset x y)
      ( is-prop-prod
          ( is-prop-neg)
          ( is-prop-leq-total-decidable-Poset y x))

  is-set-element-total-decidable-Poset : is-set element-total-decidable-Poset
  is-set-element-total-decidable-Poset =
    is-set-prop-in-id
      ( λ x y → leq-total-decidable-Poset x y × leq-total-decidable-Poset y x)
      ( λ x y →
        is-prop-prod
          ( is-prop-leq-total-decidable-Poset x y)
          ( is-prop-leq-total-decidable-Poset y x))
      ( λ x →
        pair
          ( refl-leq-total-decidable-Poset x)
          ( refl-leq-total-decidable-Poset x))
      ( λ {x y (pair H K) → antisymmetric-leq-total-decidable-Poset x y H K})

  element-total-decidable-poset-Set : Set l1
  pr1 element-total-decidable-poset-Set = element-total-decidable-Poset
  pr2 element-total-decidable-poset-Set = is-set-element-total-decidable-Poset
```
