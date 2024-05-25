# Modal logic subformulas

```agda
module modal-logic.subformulas where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.function-types
open import foundation-core.sets
open import foundation-core.subtypes

open import lists.concatenation-lists
open import lists.lists
open import lists.lists-subtypes

open import modal-logic.closed-under-subformulas-theories
open import modal-logic.deduction
open import modal-logic.formulas

open import univalent-combinatorics.kuratowsky-finite-sets
```

</details>

## Idea

The subformulas of a modal formula are the formulas that occur in the formula.

## Definition

```agda
module _
  {l : Level} {i : Set l}
  where

  subformulas-list : modal-formula i → list (modal-formula i)
  subformulas-list a = cons a (rest a)
    where
    rest : modal-formula i → list (modal-formula i)
    rest (varₘ x) = nil
    rest ⊥ₘ = nil
    rest (a →ₘ b) = concat-list (subformulas-list a) (subformulas-list b)
    rest (□ₘ a) = subformulas-list a

  subformulas : modal-formula i → modal-theory l i
  subformulas a = list-subtype (subformulas-list a)

  subformulas-list-has-subimpl :
    (a : modal-formula i) {x y : modal-formula i} →
    (x →ₘ y) ∈-list subformulas-list a →
    (x ∈-list subformulas-list a) × (y ∈-list subformulas-list a)
  subformulas-list-has-subimpl .(x →ₘ y) {x} {y} (is-head .(x →ₘ y) _) =
    pair
      ( is-in-tail x (x →ₘ y) _
        ( in-concat-left
          ( subformulas-list x)
          ( subformulas-list y)
          ( is-head x _)))
      ( is-in-tail y (x →ₘ y) _
        ( in-concat-right
          ( subformulas-list x)
          ( subformulas-list y)
          ( is-head y _)))
  subformulas-list-has-subimpl
    (a →ₘ b) {x} {y} (is-in-tail .(x →ₘ y) .(a →ₘ b) _ xy-list-subtype)
    with
    in-concat-list
      ( subformulas-list a)
      ( subformulas-list b)
      ( xy-list-subtype)
  ... | inl xy-in-left =
    let (x-in-tail , y-in-tail) = subformulas-list-has-subimpl a xy-in-left
    in pair
      ( is-in-tail x (a →ₘ b) _
        ( in-concat-left (subformulas-list a) (subformulas-list b) x-in-tail))
      ( is-in-tail y (a →ₘ b) _
        ( in-concat-left (subformulas-list a) (subformulas-list b) y-in-tail))
  ... | inr xy-in-right =
    let (x-in-tail , y-in-tail) = subformulas-list-has-subimpl b xy-in-right
    in pair
      ( is-in-tail x (a →ₘ b) _
        ( in-concat-right (subformulas-list a) (subformulas-list b) x-in-tail))
      ( is-in-tail y (a →ₘ b) _
        ( in-concat-right (subformulas-list a) (subformulas-list b) y-in-tail))
  subformulas-list-has-subimpl
    (□ₘ a) {x} {y} (is-in-tail .(x →ₘ y) .(□ₘ a) _ xy-list-subtype) =
      let (x-in-tail , y-in-tail) =
            subformulas-list-has-subimpl a xy-list-subtype
      in (is-in-tail x (□ₘ a) _ x-in-tail) , (is-in-tail y (□ₘ a) _ y-in-tail)

  subformulas-list-has-subbox :
    (a : modal-formula i) {x : modal-formula i} →
    □ₘ x ∈-list subformulas-list a →
    x ∈-list subformulas-list a
  subformulas-list-has-subbox .(□ₘ x) {x} (is-head .(□ₘ x) _) =
    is-in-tail x (□ₘ x) _ (is-head x _)
  subformulas-list-has-subbox
    (a →ₘ b) {x} (is-in-tail .(□ₘ x) .(a →ₘ b) _ x-list-subtype)
    with
      in-concat-list (subformulas-list a) (subformulas-list b) x-list-subtype
  ... | inl x-in-left =
    is-in-tail x (a →ₘ b) _
      ( in-concat-left (subformulas-list a) (subformulas-list b)
        ( subformulas-list-has-subbox a x-in-left))
  ... | inr x-in-right =
    is-in-tail x (a →ₘ b) _
      ( in-concat-right (subformulas-list a) (subformulas-list b)
        ( subformulas-list-has-subbox b x-in-right))
  subformulas-list-has-subbox
    (□ₘ a) {x} (is-in-tail .(□ₘ x) .(□ₘ a) _ x-list-subtype) =
    is-in-tail x (□ₘ a) _ (subformulas-list-has-subbox a x-list-subtype)

  is-modal-theory-has-subboxes-subformulas :
    (a : modal-formula i) → is-modal-theory-has-subboxes (subformulas a)
  is-modal-theory-has-subboxes-subformulas a =
    map-trunc-Prop (subformulas-list-has-subbox a)

  is-modal-theory-has-subimps-subformulas :
    (a : modal-formula i) → is-modal-theory-has-subimps (subformulas a)
  is-modal-theory-has-subimps-subformulas a =
    map-distributive-trunc-product-Prop ∘
      map-trunc-Prop (subformulas-list-has-subimpl a)

  is-modal-theory-closed-under-subformulas-subformulas :
    (a : modal-formula i) →
    is-modal-theory-closed-under-subformulas (subformulas a)
  is-modal-theory-closed-under-subformulas-subformulas a =
    pair
      ( is-modal-theory-has-subboxes-subformulas a)
      ( is-modal-theory-has-subimps-subformulas a)

  is-kuratowsky-finite-subformulas-list :
    (a : modal-formula i) →
    is-kuratowsky-finite-set (set-subset (modal-formula-Set i) (subformulas a))
  is-kuratowsky-finite-subformulas-list a =
    is-kuratowski-finite-list-subtype (modal-formula-Set i) (subformulas-list a)
```
