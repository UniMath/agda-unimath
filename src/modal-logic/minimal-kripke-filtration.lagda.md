# Minimal Kripke filtration

```agda
module modal-logic.minimal-kripke-filtration where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.existential-quantification
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.raising-universe-levels
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtypes

open import modal-logic.closed-under-subformulas-theories
open import modal-logic.deduction
open import modal-logic.formulas
open import modal-logic.kripke-models-filtrations
open import modal-logic.kripke-semantics
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {i : Set l3}
  (theory : modal-theory l5 i)
  (M : kripke-model l1 l2 i l4)
  where

  minimal-kripke-model-filtration :
    kripke-model
      ( lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
      ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
      ( i)
      ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  pr1 (pr1 minimal-kripke-model-filtration) =
    equivalence-class (Φ-equivalence theory M)
  pr2 (pr1 minimal-kripke-model-filtration) =
    map-is-inhabited
      ( class (Φ-equivalence theory M))
      ( is-inhabited-type-kripke-model i M)
  pr1 (pr2 minimal-kripke-model-filtration) x* y* =
    exists-structure-Prop ( type-kripke-model i M × type-kripke-model i M)
      ( λ (x , y) →
        relation-kripke-model i M x y ×
        is-in-equivalence-class (Φ-equivalence theory M) x* x ×
        is-in-equivalence-class (Φ-equivalence theory M) y* y)
  pr2 (pr2 minimal-kripke-model-filtration) n x* =
    function-Prop
      ( is-in-subtype theory (varₘ n))
      ( Π-Prop (type-kripke-model i M)
        ( λ x →
          function-Prop
            ( is-in-equivalence-class (Φ-equivalence theory M) x* x)
            ( valuate-kripke-model i M n x)))
```

## Properties

### Minimal kripke filtration is a filtration function

```agda
  module _
    (theory-is-closed : is-modal-theory-closed-under-subformulas theory)
    where

    is-kripke-model-filtration-minimal-kripke-model-filtration :
      is-kripke-model-filtration theory M minimal-kripke-model-filtration
    pr1 is-kripke-model-filtration-minimal-kripke-model-filtration =
      id-equiv
    pr1 (pr2 is-kripke-model-filtration-minimal-kripke-model-filtration)
      n in-theory x =
        pair
          ( λ val-n in-theory y eq-xy →
            map-inv-raise
              ( forward-implication
                ( eq-xy (varₘ n) in-theory)
                ( map-raise val-n)))
          ( λ val-n → val-n in-theory x (λ _ _ → id-iff))
    pr1 (pr2 (pr2 is-kripke-model-filtration-minimal-kripke-model-filtration))
      x y r =
        intro-exists (x , y) (r , (λ _ _ → id-iff) , (λ _ _ → id-iff))
    pr2 (pr2 (pr2 is-kripke-model-filtration-minimal-kripke-model-filtration))
      a box-in-theory x y r-xy x-forces-box =
        elim-exists
          ( (M , y) ⊨ₘ a)
          ( λ (x' , y') (r-xy' , iff-x , iff-y) →
            backward-implication
              ( iff-y a
                ( is-has-subboxes-is-closed-under-subformulas
                  ( theory)
                  ( theory-is-closed)
                  ( box-in-theory)))
              ( forward-implication
                ( iff-x (□ₘ a) box-in-theory)
                ( x-forces-box)
                ( y')
                ( r-xy')))
          ( r-xy)
```

### Minimal kripke filtration preserves reflexivity

```agda
    minimal-filtration-preserves-reflexivity :
      is-in-subtype (reflexive-kripke-models l1 l2 i l4) M →
      is-in-subtype
        ( reflexive-kripke-models
          ( lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
          ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
          ( i)
          ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
        ( minimal-kripke-model-filtration)
    minimal-filtration-preserves-reflexivity =
      filtration-preserves-reflexivity theory M
        ( minimal-kripke-model-filtration)
        ( is-kripke-model-filtration-minimal-kripke-model-filtration)
```

### Minimal kripke filtration preserves symmetry

```agda
    minimal-filtration-preserves-symmetry :
      is-in-subtype (symmetry-kripke-models l1 l2 i l4) M →
      is-in-subtype
        ( symmetry-kripke-models
          ( lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
          ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
          ( i)
          ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
        ( minimal-kripke-model-filtration)
    minimal-filtration-preserves-symmetry is-sym x* y* =
      elim-exists
        ( relation-Prop-kripke-model i minimal-kripke-model-filtration y* x*)
        ( λ (x , y) (r-xy , x-in-x* , y-in-y*) →
          intro-exists (y , x) (is-sym x y r-xy , y-in-y* , x-in-x*))

-- module _
--   {l1 l2 l3 l4 l5 : Level} {i : Set l3}
--   where

--   test :
--     is-class-filtration-function i l2 l3 l4 l5 (all-models _ _ i _)
--       ( minimal-kripke-model-filtration)
--   test theory is-closed (M , _) =
--     is-kripke-model-filtration-minimal-kripke-model-filtration theory M is-closed
```
