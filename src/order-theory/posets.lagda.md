# Posets

```agda
module order-theory.posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Idea

A **poset** is a set equipped with a reflexive, antisymmetric, transitive
relation that takes values in propositions.

## Definition

```agda
is-antisymmetric-leq-Preorder :
  {l1 l2 : Level} (P : Preorder l1 l2) → UU (l1 ⊔ l2)
is-antisymmetric-leq-Preorder P =
  (x y : type-Preorder P) → leq-Preorder P x y → leq-Preorder P y x → x ＝ y

Poset : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Poset l1 l2 =
  Σ (Preorder l1 l2) is-antisymmetric-leq-Preorder

module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  preorder-Poset : Preorder l1 l2
  preorder-Poset = pr1 X

  type-Poset : UU l1
  type-Poset = type-Preorder preorder-Poset

  leq-Poset-Prop : (x y : type-Poset) → Prop l2
  leq-Poset-Prop = leq-Preorder-Prop preorder-Poset

  leq-Poset : (x y : type-Poset) → UU l2
  leq-Poset = leq-Preorder preorder-Poset

  is-prop-leq-Poset : (x y : type-Poset) → is-prop (leq-Poset x y)
  is-prop-leq-Poset = is-prop-leq-Preorder preorder-Poset

  concatenate-eq-leq-Poset :
    {x y z : type-Poset} → x ＝ y → leq-Poset y z → leq-Poset x z
  concatenate-eq-leq-Poset = concatenate-eq-leq-Preorder preorder-Poset

  concatenate-leq-eq-Poset :
    {x y z : type-Poset} → leq-Poset x y → y ＝ z → leq-Poset x z
  concatenate-leq-eq-Poset = concatenate-leq-eq-Preorder preorder-Poset

  refl-leq-Poset : (x : type-Poset) → leq-Poset x x
  refl-leq-Poset = refl-leq-Preorder preorder-Poset

  transitive-leq-Poset :
    (x y z : type-Poset) → leq-Poset y z → leq-Poset x y → leq-Poset x z
  transitive-leq-Poset = transitive-leq-Preorder preorder-Poset

  le-Poset-Prop : (x y : type-Poset) → Prop (l1 ⊔ l2)
  le-Poset-Prop = le-Preorder-Prop preorder-Poset

  le-Poset : (x y : type-Poset) → UU (l1 ⊔ l2)
  le-Poset = le-Preorder preorder-Poset

  is-prop-le-Poset :
    (x y : type-Poset) → is-prop (le-Poset x y)
  is-prop-le-Poset = is-prop-le-Preorder preorder-Poset

  antisymmetric-leq-Poset :
    (x y : type-Poset) → leq-Poset x y → leq-Poset y x → Id x y
  antisymmetric-leq-Poset = pr2 X

  is-set-type-Poset : is-set type-Poset
  is-set-type-Poset =
    is-set-prop-in-id
      ( λ x y → leq-Poset x y × leq-Poset y x)
      ( λ x y → is-prop-prod (is-prop-leq-Poset x y) (is-prop-leq-Poset y x))
      ( λ x → pair (refl-leq-Poset x) (refl-leq-Poset x))
      ( λ {x y (pair H K) → antisymmetric-leq-Poset x y H K})

  set-Poset : Set l1
  pr1 set-Poset = type-Poset
  pr2 set-Poset = is-set-type-Poset
```
