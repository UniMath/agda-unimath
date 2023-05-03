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

  poset-decidable-Poset : Poset l1 l2
  poset-decidable-Poset = pr1 X

  is-decidable-poset-decidable-Poset : is-decidable-Poset (poset-decidable-Poset)
  is-decidable-poset-decidable-Poset = pr2 X

  element-decidable-Poset : UU l1
  element-decidable-Poset = element-Poset poset-decidable-Poset

  leq-decidable-poset-Prop : (x y : element-decidable-Poset) → Prop l2
  leq-decidable-poset-Prop = leq-poset-Prop poset-decidable-Poset

  leq-decidable-Poset : (x y : element-decidable-Poset) → UU l2
  leq-decidable-Poset = leq-Poset poset-decidable-Poset

  is-prop-leq-decidable-Poset :
    (x y : element-decidable-Poset) → is-prop (leq-decidable-Poset x y)
  is-prop-leq-decidable-Poset = is-prop-leq-Poset poset-decidable-Poset

  preorder-decidable-Poset : Preorder l1 l2
  preorder-decidable-Poset = preorder-Poset poset-decidable-Poset

  decidable-preorder-decidable-Poset : decidable-Preorder l1 l2
  pr1 decidable-preorder-decidable-Poset = preorder-decidable-Poset
  pr2 decidable-preorder-decidable-Poset = is-decidable-poset-decidable-Poset

  leq-decidable-poset-decidable-Prop :
    (x y : element-decidable-Poset) → decidable-Prop l2
  leq-decidable-poset-decidable-Prop =
    leq-decidable-preorder-decidable-Prop decidable-preorder-decidable-Poset

  concatenate-eq-leq-decidable-Poset :
    {x y z : element-decidable-Poset} → x ＝ y →
    leq-decidable-Poset y z → leq-decidable-Poset x z
  concatenate-eq-leq-decidable-Poset =
    concatenate-eq-leq-Poset poset-decidable-Poset

  concatenate-leq-eq-decidable-Poset :
    {x y z : element-decidable-Poset} →
    leq-decidable-Poset x y → y ＝ z → leq-decidable-Poset x z
  concatenate-leq-eq-decidable-Poset =
    concatenate-leq-eq-Poset poset-decidable-Poset

  refl-leq-decidable-Poset :
    (x : element-decidable-Poset) → leq-decidable-Poset x x
  refl-leq-decidable-Poset = refl-leq-Poset poset-decidable-Poset

  transitive-leq-decidable-Poset :
    (x y z : element-decidable-Poset) → leq-decidable-Poset y z →
    leq-decidable-Poset x y → leq-decidable-Poset x z
  transitive-leq-decidable-Poset = transitive-leq-Poset poset-decidable-Poset

  antisymmetric-leq-decidable-Poset :
    (x y : element-decidable-Poset) →
    leq-decidable-Poset x y → leq-decidable-Poset y x → Id x y
  antisymmetric-leq-decidable-Poset =
    antisymmetric-leq-Poset poset-decidable-Poset

  is-set-element-decidable-Poset : is-set element-decidable-Poset
  is-set-element-decidable-Poset = is-set-element-Poset poset-decidable-Poset

  element-decidable-poset-Set : Set l1
  element-decidable-poset-Set = element-poset-Set poset-decidable-Poset
```
