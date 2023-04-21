# Totally ordered posets

```agda
module order-theory.total-posets where
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

### Being a totally order poset

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

### Type of total posets

```agda
total-Poset : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
total-Poset l1 l2 = Σ (Poset l1 l2) is-total-Poset

module _
  {l1 l2 : Level} (X : total-Poset l1 l2)
  where

  Poset-total-Poset : Poset l1 l2
  Poset-total-Poset = pr1 X

  is-total-Poset-total-Poset : is-total-Poset (Poset-total-Poset)
  is-total-Poset-total-Poset = pr2 X

  element-total-Poset : UU l1
  element-total-Poset = pr1 Poset-total-Poset

  leq-total-poset-Prop : (x y : element-total-Poset) → Prop l2
  leq-total-poset-Prop = pr1 (pr2 Poset-total-Poset)

  leq-total-Poset : (x y : element-total-Poset) → UU l2
  leq-total-Poset x y = type-Prop (leq-total-poset-Prop x y)

  is-prop-leq-total-Poset :
    (x y : element-total-Poset) → is-prop (leq-total-Poset x y)
  is-prop-leq-total-Poset x y = is-prop-type-Prop (leq-total-poset-Prop x y)

  concatenate-eq-leq-total-Poset :
    {x y z : element-total-Poset} → x ＝ y →
    leq-total-Poset y z → leq-total-Poset x z
  concatenate-eq-leq-total-Poset refl H = H

  concatenate-leq-eq-total-Poset :
    {x y z : element-total-Poset} →
    leq-total-Poset x y → y ＝ z → leq-total-Poset x z
  concatenate-leq-eq-total-Poset H refl = H

  refl-leq-total-Poset : (x : element-total-Poset) → leq-total-Poset x x
  refl-leq-total-Poset = pr1 (pr1 (pr2 (pr2 Poset-total-Poset)))

  transitive-leq-total-Poset :
    (x y z : element-total-Poset) → leq-total-Poset y z →
    leq-total-Poset x y → leq-total-Poset x z
  transitive-leq-total-Poset = pr2 (pr1 (pr2 (pr2 Poset-total-Poset)))

  preorder-total-Poset : Preorder l1 l2
  pr1 preorder-total-Poset = element-total-Poset
  pr1 (pr2 preorder-total-Poset) = leq-total-poset-Prop
  pr1 (pr2 (pr2 preorder-total-Poset)) = refl-leq-total-Poset
  pr2 (pr2 (pr2 preorder-total-Poset)) = transitive-leq-total-Poset

  antisymmetric-leq-total-Poset :
    (x y : element-total-Poset) →
    leq-total-Poset x y → leq-total-Poset y x → Id x y
  antisymmetric-leq-total-Poset = pr2 (pr2 (pr2 Poset-total-Poset))

  is-set-element-total-Poset : is-set element-total-Poset
  is-set-element-total-Poset =
    is-set-prop-in-id
      ( λ x y → leq-total-Poset x y × leq-total-Poset y x)
      ( λ x y →
        is-prop-prod (is-prop-leq-total-Poset x y) (is-prop-leq-total-Poset y x))
      ( λ x → pair (refl-leq-total-Poset x) (refl-leq-total-Poset x))
      ( λ {x y (pair H K) → antisymmetric-leq-total-Poset x y H K})

  element-total-poset-Set : Set l1
  pr1 element-total-poset-Set = element-total-Poset
  pr2 element-total-poset-Set = is-set-element-total-Poset
```
