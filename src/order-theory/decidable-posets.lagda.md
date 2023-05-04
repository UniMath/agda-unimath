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

## Idea

A **decidable poset** is a poset of which the ordering relation is decidable. It
follows that decidable posets have decidable equality.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-decidable-Poset-Prop : Prop (l1 ⊔ l2)
  is-decidable-Poset-Prop = is-decidable-Preorder-Prop (preorder-Poset X)

  is-decidable-Poset : UU (l1 ⊔ l2)
  is-decidable-Poset = type-Prop is-decidable-Poset-Prop

  is-prop-is-decidable-Poset : is-prop is-decidable-Poset
  is-prop-is-decidable-Poset = is-prop-type-Prop is-decidable-Poset-Prop

Decidable-Poset : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Decidable-Poset l1 l2 = Σ (Poset l1 l2) is-decidable-Poset

module _
  {l1 l2 : Level} (X : Decidable-Poset l1 l2)
  where

  poset-Decidable-Poset : Poset l1 l2
  poset-Decidable-Poset = pr1 X

  is-decidable-poset-Decidable-Poset :
    is-decidable-Poset (poset-Decidable-Poset)
  is-decidable-poset-Decidable-Poset = pr2 X

  element-Decidable-Poset : UU l1
  element-Decidable-Poset = element-Poset poset-Decidable-Poset

  leq-Decidable-Poset-Prop : (x y : element-Decidable-Poset) → Prop l2
  leq-Decidable-Poset-Prop = leq-Poset-Prop poset-Decidable-Poset

  leq-Decidable-Poset : (x y : element-Decidable-Poset) → UU l2
  leq-Decidable-Poset = leq-Poset poset-Decidable-Poset

  is-prop-leq-Decidable-Poset :
    (x y : element-Decidable-Poset) → is-prop (leq-Decidable-Poset x y)
  is-prop-leq-Decidable-Poset = is-prop-leq-Poset poset-Decidable-Poset

  preorder-Decidable-Poset : Preorder l1 l2
  preorder-Decidable-Poset = preorder-Poset poset-Decidable-Poset

  decidable-preorder-Decidable-Poset : decidable-Preorder l1 l2
  pr1 decidable-preorder-Decidable-Poset = preorder-Decidable-Poset
  pr2 decidable-preorder-Decidable-Poset = is-decidable-poset-Decidable-Poset

  leq-decidable-poset-decidable-Prop :
    (x y : element-Decidable-Poset) → Decidable-Prop l2
  leq-decidable-poset-decidable-Prop =
    leq-decidable-preorder-decidable-Prop decidable-preorder-Decidable-Poset

  concatenate-eq-leq-Decidable-Poset :
    {x y z : element-Decidable-Poset} → x ＝ y →
    leq-Decidable-Poset y z → leq-Decidable-Poset x z
  concatenate-eq-leq-Decidable-Poset =
    concatenate-eq-leq-Poset poset-Decidable-Poset

  concatenate-leq-eq-Decidable-Poset :
    {x y z : element-Decidable-Poset} →
    leq-Decidable-Poset x y → y ＝ z → leq-Decidable-Poset x z
  concatenate-leq-eq-Decidable-Poset =
    concatenate-leq-eq-Poset poset-Decidable-Poset

  refl-leq-Decidable-Poset :
    (x : element-Decidable-Poset) → leq-Decidable-Poset x x
  refl-leq-Decidable-Poset = refl-leq-Poset poset-Decidable-Poset

  transitive-leq-Decidable-Poset :
    (x y z : element-Decidable-Poset) → leq-Decidable-Poset y z →
    leq-Decidable-Poset x y → leq-Decidable-Poset x z
  transitive-leq-Decidable-Poset = transitive-leq-Poset poset-Decidable-Poset

  antisymmetric-leq-Decidable-Poset :
    (x y : element-Decidable-Poset) →
    leq-Decidable-Poset x y → leq-Decidable-Poset y x → Id x y
  antisymmetric-leq-Decidable-Poset =
    antisymmetric-leq-Poset poset-Decidable-Poset

  is-set-element-Decidable-Poset : is-set element-Decidable-Poset
  is-set-element-Decidable-Poset = is-set-element-Poset poset-Decidable-Poset

  element-decidable-poset-Set : Set l1
  element-decidable-poset-Set = element-poset-Set poset-Decidable-Poset
```
