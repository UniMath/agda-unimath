# Minimal transitive Kripke filtration

```agda
module modal-logic.minimal-transitive-kripke-filtration where
```

<details><summary>Imports</summary>

```agda
open import foundation.transitive-closures-binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtypes

open import modal-logic.axioms
open import modal-logic.closed-under-subformulas-theories
open import modal-logic.deduction
open import modal-logic.formulas
open import modal-logic.kripke-models-filtrations
open import modal-logic.kripke-semantics
open import modal-logic.minimal-kripke-filtration
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

  minimal-transitive-kripke-model-filtration :
    kripke-model
      ( lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
      ( lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
      ( i)
      ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  pr1 minimal-transitive-kripke-model-filtration =
    Inhabited-Type-kripke-model i (minimal-kripke-model-filtration theory M)
  pr1 (pr2 minimal-transitive-kripke-model-filtration) =
    transitive-closure-Relation-Prop
      ( relation-Prop-kripke-model i (minimal-kripke-model-filtration theory M))
  pr2 (pr2 minimal-transitive-kripke-model-filtration) =
    valuate-kripke-model i (minimal-kripke-model-filtration theory M)
```

## Properties

### Minimal transitive kripke filtration is transitive

```agda
  minimal-transitive-filtration-is-transitive :
    is-in-subtype
      ( transitive-kripke-models
        ( lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
        ( lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
        ( i)
        ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
      ( minimal-transitive-kripke-model-filtration)
  minimal-transitive-filtration-is-transitive =
    is-transitive-transitive-closure-Relation-Prop
      ( relation-Prop-kripke-model i
        ( minimal-kripke-model-filtration theory M))
```

### Minimal transitive filtration is a filtration function

```agda
  module _
    (theory-is-closed : is-modal-theory-closed-under-subformulas theory)
    where

    is-filtration-minimal-transitive-kripke-model-filtration :
      is-in-subtype (transitive-kripke-models l1 l2 i l4) M →
      is-kripke-model-filtration theory M
        ( minimal-transitive-kripke-model-filtration)
    pr1 (is-filtration-minimal-transitive-kripke-model-filtration M-is-trans) =
      equiv-is-kripke-model-filtration theory M
        ( minimal-kripke-model-filtration theory M)
        ( is-kripke-model-filtration-minimal-kripke-model-filtration theory M
          ( theory-is-closed))
    pr1 (pr2
      (is-filtration-minimal-transitive-kripke-model-filtration M-is-trans)) =
        is-filtration-valuate-is-kripke-model-filtration theory M
          ( minimal-kripke-model-filtration theory M)
          ( is-kripke-model-filtration-minimal-kripke-model-filtration theory M
            ( theory-is-closed))
    pr1 (pr2 (pr2
      (is-filtration-minimal-transitive-kripke-model-filtration M-is-trans)))
        x y r =
          -- TODO: Refactor
          unit-trunc-Prop
            ( base-transitive-closure-Relation
              ( filtration-relation-lower-bound-is-kripke-model-filtration
                ( theory)
                ( M)
                ( minimal-kripke-model-filtration theory M)
                ( is-kripke-model-filtration-minimal-kripke-model-filtration
                  ( theory)
                  ( M)
                  ( theory-is-closed))
                ( x)
                ( y)
                ( r)))
    pr2 (pr2 (pr2
      (is-filtration-minimal-transitive-kripke-model-filtration M-is-trans)))
        a box-in-theory x y r-xy x-forces-box =
          apply-universal-property-trunc-Prop
            ( r-xy)
            ( (M , y) ⊨ₘ a)
            ( λ r → α x r x-forces-box)
      where
      α :
        (x : type-kripke-model i M) →
        transitive-closure-Relation
          ( relation-kripke-model i (minimal-kripke-model-filtration theory M))
          ( class (Φ-equivalence theory M) x)
          ( class (Φ-equivalence theory M) y) →
        type-Prop ((M , x) ⊨ₘ □ₘ a) →
        type-Prop ((M , y) ⊨ₘ a)
      α x (base-transitive-closure-Relation r) x-forces-box =
        filtration-relation-upper-bound-is-kripke-model-filtration theory M
          ( minimal-kripke-model-filtration theory M)
          ( is-kripke-model-filtration-minimal-kripke-model-filtration theory M
            ( theory-is-closed))
          ( a)
          ( box-in-theory)
          ( x)
          ( y)
          ( r)
          ( x-forces-box)
      α x (step-transitive-closure-Relation {y = z*} r-xz c-zy) x-forces-box =
        apply-universal-property-trunc-Prop
          ( is-inhabited-subtype-equivalence-class (Φ-equivalence theory M) z*)
          ( (M , y) ⊨ₘ a)
          ( λ (z , z-in-z*) →
            β z
              (eq-class-equivalence-class (Φ-equivalence theory M) z* z-in-z*))
        where
        β :
          (z : type-kripke-model i M) →
          class (Φ-equivalence theory M) z ＝ z* →
          type-Prop ((M , y) ⊨ₘ a)
        β z refl =
          apply-universal-property-trunc-Prop
            ( r-xz)
            ( (M , y) ⊨ₘ a)
            ( λ ((x' , z') , r-xz' , iff-x , iff-z) →
              α z c-zy
                ( backward-implication
                  ( iff-z (□ₘ a) box-in-theory)
                  ( ax-4-soundness i _ _ _ (a , refl) M M-is-trans
                    ( x')
                    ( forward-implication
                      ( iff-x (□ₘ a) box-in-theory)
                      ( x-forces-box))
                    ( z')
                    ( r-xz'))))
```

### Minimal transitive kripke filtration preserves symmetry

```agda
    minimal-transitive-filtration-preserves-reflexivity :
      is-in-subtype (reflexive-kripke-models l1 l2 i l4) M →
      is-in-subtype
        ( reflexive-kripke-models
          ( lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
          ( lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
          ( i)
          ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
        ( minimal-transitive-kripke-model-filtration)
    minimal-transitive-filtration-preserves-reflexivity is-refl =
      is-reflexive-transitive-closure-is-reflexive-Relation-Prop
        ( relation-Prop-kripke-model i
          ( minimal-kripke-model-filtration theory M))
        ( minimal-filtration-preserves-reflexivity theory M theory-is-closed
          ( is-refl))
```

### Minimal transitive kripke filtration preserves symmetry

```agda
    minimal-transitive-filtration-preserves-symmetry :
      is-in-subtype (symmetry-kripke-models l1 l2 i l4) M →
      is-in-subtype
        ( symmetry-kripke-models
          ( lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
          ( lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
          ( i)
          ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
        ( minimal-transitive-kripke-model-filtration)
    minimal-transitive-filtration-preserves-symmetry is-sym =
      is-symmetric-transitive-closure-is-symmetric-Relation-Prop
        ( relation-Prop-kripke-model i
          ( minimal-kripke-model-filtration theory M))
        ( minimal-filtration-preserves-symmetry theory M theory-is-closed
          ( is-sym))
```

### Minimal transitive kripke filtration preserves equivalence

```agda
    minimal-transitive-filtration-preserves-equivalence :
      is-in-subtype (equivalence-kripke-models l1 l2 i l4) M →
      is-in-subtype
        ( equivalence-kripke-models
          ( lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
          ( lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
          ( i)
          ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
        ( minimal-transitive-kripke-model-filtration)
    minimal-transitive-filtration-preserves-equivalence (is-refl , is-sym , _) =
      triple
        ( minimal-transitive-filtration-preserves-reflexivity is-refl)
        ( minimal-transitive-filtration-preserves-symmetry is-sym)
        ( minimal-transitive-filtration-is-transitive)
```
