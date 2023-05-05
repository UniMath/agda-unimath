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

A poset is a set equipped with a reflexive, antisymmetric, transitive relation
that takes values in propositions.

## Definition

```agda
Poset : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Poset l1 l2 =
  Σ ( UU l1)
    ( λ X →
      Σ ( X → X → Prop l2)
        ( λ R →
          ( ( (x : X) → type-Prop (R x x)) ×
            ( (x y z : X) →
              type-Prop (R y z) → type-Prop (R x y) → type-Prop (R x z))) ×
          ( (x y : X) → type-Prop (R x y) → type-Prop (R y x) → Id x y)))

module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  type-Poset : UU l1
  type-Poset = pr1 X

  leq-Poset-Prop : (x y : type-Poset) → Prop l2
  leq-Poset-Prop = pr1 (pr2 X)

  leq-Poset : (x y : type-Poset) → UU l2
  leq-Poset x y = type-Prop (leq-Poset-Prop x y)

  is-prop-leq-Poset : (x y : type-Poset) → is-prop (leq-Poset x y)
  is-prop-leq-Poset x y = is-prop-type-Prop (leq-Poset-Prop x y)

  concatenate-eq-leq-Poset :
    {x y z : type-Poset} → x ＝ y → leq-Poset y z → leq-Poset x z
  concatenate-eq-leq-Poset refl H = H

  concatenate-leq-eq-Poset :
    {x y z : type-Poset} → leq-Poset x y → y ＝ z → leq-Poset x z
  concatenate-leq-eq-Poset H refl = H

  refl-leq-Poset : (x : type-Poset) → leq-Poset x x
  refl-leq-Poset = pr1 (pr1 (pr2 (pr2 X)))

  transitive-leq-Poset :
    (x y z : type-Poset) → leq-Poset y z → leq-Poset x y → leq-Poset x z
  transitive-leq-Poset = pr2 (pr1 (pr2 (pr2 X)))

  preorder-Poset : Preorder l1 l2
  pr1 preorder-Poset = type-Poset
  pr1 (pr2 preorder-Poset) = leq-Poset-Prop
  pr1 (pr2 (pr2 preorder-Poset)) = refl-leq-Poset
  pr2 (pr2 (pr2 preorder-Poset)) = transitive-leq-Poset

  le-Poset-Prop : (x y : type-Poset) → Prop (l1 ⊔ l2)
  le-Poset-Prop = le-Preorder-Prop preorder-Poset

  le-Poset : (x y : type-Poset) → UU (l1 ⊔ l2)
  le-Poset = le-Preorder preorder-Poset

  is-prop-le-Poset :
    (x y : type-Poset) → is-prop (le-Poset x y)
  is-prop-le-Poset = is-prop-le-Preorder preorder-Poset

  antisymmetric-leq-Poset :
    (x y : type-Poset) → leq-Poset x y → leq-Poset y x → Id x y
  antisymmetric-leq-Poset = pr2 (pr2 (pr2 X))

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
