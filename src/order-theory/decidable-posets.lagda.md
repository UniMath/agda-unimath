# Decidable posets

```agda
module order-theory.decidable-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.decidable-preorders
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-decidable-poset-Prop : Prop (l1 ⊔ l2)
  is-decidable-poset-Prop = is-decidable-preorder-Prop (preorder-Poset X)

  is-decidable-Poset : UU (l1 ⊔ l2)
  is-decidable-Poset = type-Prop is-decidable-poset-Prop

  is-prop-is-decidable-Poset : is-prop is-decidable-Poset
  is-prop-is-decidable-Poset = is-prop-type-Prop is-decidable-poset-Prop

decidable-Poset : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
decidable-Poset l1 l2 = Σ (Poset l1 l2) is-decidable-Poset

module _
  {l1 l2 : Level} (X : decidable-Poset l1 l2)
  where

  Poset-decidable-Poset : Poset l1 l2
  Poset-decidable-Poset = pr1 X

  is-decidable-Poset-decidable-Poset : is-decidable-Poset (Poset-decidable-Poset)
  is-decidable-Poset-decidable-Poset = pr2 X

  element-decidable-Poset : UU l1
  element-decidable-Poset = pr1 Poset-decidable-Poset

  leq-decidable-poset-Prop : (x y : element-decidable-Poset) → Prop l2
  leq-decidable-poset-Prop = pr1 (pr2 Poset-decidable-Poset)

  leq-decidable-Poset : (x y : element-decidable-Poset) → UU l2
  leq-decidable-Poset x y = type-Prop (leq-decidable-poset-Prop x y)

  is-prop-leq-decidable-Poset :
    (x y : element-decidable-Poset) → is-prop (leq-decidable-Poset x y)
  is-prop-leq-decidable-Poset x y =
    is-prop-type-Prop (leq-decidable-poset-Prop x y)

  leq-decidable-poset-decidable-Prop :
    (x y : element-decidable-Poset) → decidable-Prop l2
  pr1 (leq-decidable-poset-decidable-Prop x y) = leq-decidable-Poset x y
  pr1 (pr2 (leq-decidable-poset-decidable-Prop x y)) =
    is-prop-leq-decidable-Poset x y
  pr2 (pr2 (leq-decidable-poset-decidable-Prop x y)) =
    is-decidable-Poset-decidable-Poset x y

  concatenate-eq-leq-decidable-Poset :
    {x y z : element-decidable-Poset} → x ＝ y →
    leq-decidable-Poset y z → leq-decidable-Poset x z
  concatenate-eq-leq-decidable-Poset refl H = H

  concatenate-leq-eq-decidable-Poset :
    {x y z : element-decidable-Poset} →
    leq-decidable-Poset x y → y ＝ z → leq-decidable-Poset x z
  concatenate-leq-eq-decidable-Poset H refl = H

  refl-leq-decidable-Poset :
    (x : element-decidable-Poset) → leq-decidable-Poset x x
  refl-leq-decidable-Poset = pr1 (pr1 (pr2 (pr2 Poset-decidable-Poset)))

  transitive-leq-decidable-Poset :
    (x y z : element-decidable-Poset) → leq-decidable-Poset y z →
    leq-decidable-Poset x y → leq-decidable-Poset x z
  transitive-leq-decidable-Poset = pr2 (pr1 (pr2 (pr2 Poset-decidable-Poset)))

  preorder-decidable-Poset : Preorder l1 l2
  pr1 preorder-decidable-Poset = element-decidable-Poset
  pr1 (pr2 preorder-decidable-Poset) = leq-decidable-poset-Prop
  pr1 (pr2 (pr2 preorder-decidable-Poset)) = refl-leq-decidable-Poset
  pr2 (pr2 (pr2 preorder-decidable-Poset)) = transitive-leq-decidable-Poset

  antisymmetric-leq-decidable-Poset :
    (x y : element-decidable-Poset) →
    leq-decidable-Poset x y → leq-decidable-Poset y x → Id x y
  antisymmetric-leq-decidable-Poset = pr2 (pr2 (pr2 Poset-decidable-Poset))

  is-set-element-decidable-Poset : is-set element-decidable-Poset
  is-set-element-decidable-Poset =
    is-set-prop-in-id
      ( λ x y → leq-decidable-Poset x y × leq-decidable-Poset y x)
      ( λ x y →
        is-prop-prod
          ( is-prop-leq-decidable-Poset x y)
          ( is-prop-leq-decidable-Poset y x))
      ( λ x → pair (refl-leq-decidable-Poset x) (refl-leq-decidable-Poset x))
      ( λ {x y (pair H K) → antisymmetric-leq-decidable-Poset x y H K})

  element-decidable-poset-Set : Set l1
  pr1 element-decidable-poset-Set = element-decidable-Poset
  pr2 element-decidable-poset-Set = is-set-element-decidable-Poset
```
