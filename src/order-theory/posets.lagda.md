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

A poset is a set equipped with a reflexive, antisymmetric, transitive relation that takes values in propositions.

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

  element-Poset : UU l1
  element-Poset = pr1 X

  leq-poset-Prop : (x y : element-Poset) → Prop l2
  leq-poset-Prop = pr1 (pr2 X)

  leq-Poset : (x y : element-Poset) →  UU l2
  leq-Poset x y = type-Prop (leq-poset-Prop x y)

  is-prop-leq-Poset : (x y : element-Poset) → is-prop (leq-Poset x y)
  is-prop-leq-Poset x y = is-prop-type-Prop (leq-poset-Prop x y)

  refl-leq-Poset : (x : element-Poset) → leq-Poset x x
  refl-leq-Poset = pr1 (pr1 (pr2 (pr2 X)))

  transitive-leq-Poset :
    (x y z : element-Poset) → leq-Poset y z → leq-Poset x y → leq-Poset x z
  transitive-leq-Poset = pr2 (pr1 (pr2 (pr2 X)))

  preorder-Poset : Preorder l1 l2
  pr1 preorder-Poset = element-Poset
  pr1 (pr2 preorder-Poset) = leq-poset-Prop
  pr1 (pr2 (pr2 preorder-Poset)) = refl-leq-Poset
  pr2 (pr2 (pr2 preorder-Poset)) = transitive-leq-Poset

  antisymmetric-leq-Poset :
    (x y : element-Poset) → leq-Poset x y → leq-Poset y x → Id x y
  antisymmetric-leq-Poset = pr2 (pr2 (pr2 X))

  is-set-element-Poset : is-set element-Poset
  is-set-element-Poset =
    is-set-prop-in-id
      ( λ x y → leq-Poset x y × leq-Poset y x)
      ( λ x y → is-prop-prod (is-prop-leq-Poset x y) (is-prop-leq-Poset y x))
      ( λ x → pair (refl-leq-Poset x) (refl-leq-Poset x))
      ( λ {x y (pair H K) → antisymmetric-leq-Poset x y H K})

  element-poset-Set : Set l1
  pr1 element-poset-Set = element-Poset
  pr2 element-poset-Set = is-set-element-Poset
```
