# Formulas deduction

```agda
module modal-logic.formulas-deduction where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.sets
open import foundation.subtypes
open import foundation.unions-subtypes
open import foundation.universe-levels

open import foundation-core.identity-types

open import modal-logic.axioms
open import modal-logic.deduction
open import modal-logic.formulas
open import modal-logic.modal-logic-k
open import modal-logic.weak-deduction
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 l2 : Level} (i : Set l1)
  (axioms : modal-theory l2 i)
  (is-normal : is-normal-modal-logic axioms)
  where

  private
    contains-ax-k : ax-k i ⊆ axioms
    contains-ax-k =
      transitive-leq-subtype
        ( ax-k i)
        ( modal-logic-K i)
        ( axioms)
        ( is-normal)
        ( K-contains-ax-k i)

    contains-ax-s : ax-s i ⊆ axioms
    contains-ax-s =
      transitive-leq-subtype
        ( ax-s i)
        ( modal-logic-K i)
        ( axioms)
        ( is-normal)
        ( K-contains-ax-s i)

    contains-ax-n : ax-n i ⊆ axioms
    contains-ax-n =
      transitive-leq-subtype
        ( ax-n i)
        ( modal-logic-K i)
        ( axioms)
        ( is-normal)
        ( K-contains-ax-n i)

    contains-ax-dn : ax-dn i ⊆ axioms
    contains-ax-dn =
      transitive-leq-subtype
        ( ax-dn i)
        ( modal-logic-K i)
        ( axioms)
        ( is-normal)
        ( K-contains-ax-dn i)

  weak-modal-logic-const :
    (a : modal-formula i) {b : modal-formula i} →
    is-in-subtype (weak-modal-logic-closure axioms) b →
    is-in-subtype (weak-modal-logic-closure axioms) (a →ₘ b)
  weak-modal-logic-const a {b} b-in-logic =
    weak-modal-logic-closure-mp
      ( weak-modal-logic-closure-ax
        ( contains-ax-k (b →ₘ a →ₘ b) (b , a , refl)))
      ( b-in-logic)

  modal-logic-const :
    (a : modal-formula i) {b : modal-formula i} →
    is-in-subtype (modal-logic-closure axioms) b →
    is-in-subtype (modal-logic-closure axioms) (a →ₘ b)
  modal-logic-const a {b} b-in-logic =
    modal-logic-closure-mp
      ( modal-logic-closure-ax
        ( contains-ax-k (b →ₘ a →ₘ b) (b , a , refl)))
      ( b-in-logic)

  weak-modal-logic-transitivity :
    {a b c : modal-formula i} →
    is-in-subtype (weak-modal-logic-closure axioms) (b →ₘ c) →
    is-in-subtype (weak-modal-logic-closure axioms) (a →ₘ b) →
    is-in-subtype (weak-modal-logic-closure axioms) (a →ₘ c)
  weak-modal-logic-transitivity {a} {b} {c} bc ab =
    weak-modal-logic-closure-mp
      ( weak-modal-logic-closure-mp
        ( weak-modal-logic-closure-ax
          ( contains-ax-s _ (a , b , c , refl)))
        ( weak-modal-logic-const a bc))
      ( ab)

  modal-logic-transitivity :
    {a b c : modal-formula i} →
    is-in-subtype (modal-logic-closure axioms) (b →ₘ c) →
    is-in-subtype (modal-logic-closure axioms) (a →ₘ b) →
    is-in-subtype (modal-logic-closure axioms) (a →ₘ c)
  modal-logic-transitivity {a} {b} {c} bc ab =
    modal-logic-closure-mp
      ( modal-logic-closure-mp
        ( modal-logic-closure-ax
          ( contains-ax-s _ (a , b , c , refl)))
        ( modal-logic-const a bc))
      ( ab)

  modal-logic-implication-box' :
    {a b : modal-formula i} →
    is-in-subtype (modal-logic-closure axioms) (a →ₘ b) →
    is-in-subtype (modal-logic-closure axioms) (□ₘ a →ₘ □ₘ b)
  modal-logic-implication-box' {a} {b} ab =
    modal-logic-closure-mp
      ( modal-logic-closure-ax
        ( contains-ax-n (□ₘ (a →ₘ b) →ₘ □ₘ a →ₘ □ₘ b) (a , b , refl)))
      ( modal-logic-closure-nec ab)

  modal-logic-implication-box :
    {a b : modal-formula i} →
    is-in-subtype (modal-logic-closure axioms) (a →ₘ b) →
    is-in-subtype (modal-logic-closure axioms) (□ₘ a) →
    is-in-subtype (modal-logic-closure axioms) (□ₘ b)
  modal-logic-implication-box {a} {b} ab box-a =
    modal-logic-closure-mp
      ( modal-logic-closure-mp
        ( modal-logic-closure-ax
          ( contains-ax-n (□ₘ (a →ₘ b) →ₘ □ₘ a →ₘ □ₘ b) (a , b , refl)))
        ( modal-logic-closure-nec ab))
      ( box-a)

  weak-modal-logic-implication-dn :
    (a : modal-formula i) →
    is-in-subtype (weak-modal-logic-closure axioms) (a →ₘ ¬¬ₘ a)
  weak-modal-logic-implication-dn a =
    inv-deduction-ex-falso axioms contains-ax-k contains-ax-s contains-ax-dn
    ( a)
    ( ⊥ₘ)

  modal-logic-implication-dn :
    (a : modal-formula i) →
    is-in-subtype (modal-logic-closure axioms) (a →ₘ ¬¬ₘ a)
  modal-logic-implication-dn a =
    subset-weak-modal-logic-closure-modal-logic-closure (a →ₘ ¬¬ₘ a)
      ( weak-modal-logic-implication-dn a)

  weak-modal-logic-implication-negate :
    {a b : modal-formula i} →
    is-in-subtype axioms (a →ₘ b) →
    is-in-subtype (weak-modal-logic-closure axioms) (¬ₘ b →ₘ ¬ₘ a)
  weak-modal-logic-implication-negate {a} {b} ab =
    forward-implication
      ( deduction-theorem axioms contains-ax-k contains-ax-s (¬ₘ b) (¬ₘ a))
      ( forward-implication
        ( deduction-theorem
          ( theory-add-formula (¬ₘ b) axioms)
          ( contains-ax-k')
          ( contains-ax-s')
          ( a)
          ( ⊥ₘ))
          ( logic-ex-falso
            ( theory-add-formula a (theory-add-formula (¬ₘ b) axioms))
            ( contains-ax-k'')
            ( contains-ax-s'')
            ( contains-ax-dn'')
            ( b)
            ( ⊥ₘ)
            ( weak-modal-logic-closure-mp
              ( weak-modal-logic-closure-ax
                ( subset-add-formula a (theory-add-formula (¬ₘ b) axioms)
                  ( a →ₘ b)
                  ( subset-add-formula (¬ₘ b) axioms (a →ₘ b) ab)))
              ( weak-modal-logic-closure-ax
                ( formula-in-add-formula a (theory-add-formula (¬ₘ b) axioms))))
            ( weak-modal-logic-closure-ax
              ( subset-add-formula a (theory-add-formula (¬ₘ b) axioms)
                ( ¬ₘ b)
                ( formula-in-add-formula (¬ₘ b) axioms)))))
    where
    contains-ax-k' : ax-k i ⊆ theory-add-formula (¬ₘ b) axioms
    contains-ax-k' =
      transitive-subset-add-formula (¬ₘ b) axioms (ax-k i) contains-ax-k

    contains-ax-s' : ax-s i ⊆ theory-add-formula (¬ₘ b) axioms
    contains-ax-s' =
      transitive-subset-add-formula (¬ₘ b) axioms (ax-s i) contains-ax-s

    contains-ax-k'' :
      ax-k i ⊆ theory-add-formula a (theory-add-formula (¬ₘ b) axioms)
    contains-ax-k'' =
      transitive-subset-add-formula a (theory-add-formula (¬ₘ b) axioms)
        ( ax-k i)
        ( contains-ax-k')

    contains-ax-s'' :
      ax-s i ⊆ theory-add-formula a (theory-add-formula (¬ₘ b) axioms)
    contains-ax-s'' =
      transitive-subset-add-formula a (theory-add-formula (¬ₘ b) axioms)
        ( ax-s i)
        ( contains-ax-s')

    contains-ax-dn'' :
      ax-dn i ⊆ theory-add-formula a (theory-add-formula (¬ₘ b) axioms)
    contains-ax-dn'' =
      transitive-subset-add-formula a (theory-add-formula (¬ₘ b) axioms)
        ( ax-dn i)
        ( transitive-subset-add-formula (¬ₘ b) axioms (ax-dn i) contains-ax-dn)

  modal-logic-implication-negate :
    {a b : modal-formula i} →
    is-in-subtype axioms (a →ₘ b) →
    is-in-subtype (modal-logic-closure axioms) (¬ₘ b →ₘ ¬ₘ a)
  modal-logic-implication-negate {a} {b} ab =
    subset-weak-modal-logic-closure-modal-logic-closure (¬ₘ b →ₘ ¬ₘ a)
      ( weak-modal-logic-implication-negate ab)

  modal-logic-diamond-negate :
    {a : modal-formula i} →
    is-in-subtype (modal-logic-closure axioms) (◇ₘ ¬ₘ a) →
    is-in-subtype (modal-logic-closure axioms) (¬ₘ □ₘ a)
  modal-logic-diamond-negate {a} dia-a =
    modal-logic-transitivity
      ( dia-a)
      ( modal-logic-implication-box' (modal-logic-implication-dn a))

  modal-logic-diamond-negate-implication :
    {a : modal-formula i} →
    is-modal-logic axioms →
    is-in-subtype axioms (◇ₘ ¬ₘ a →ₘ ¬ₘ □ₘ a)
  modal-logic-diamond-negate-implication {a} is-logic =
    is-logic (◇ₘ ¬ₘ a →ₘ ¬ₘ □ₘ a)
      ( modal-logic-implication-negate
        ( is-logic (□ₘ a →ₘ □ₘ ¬¬ₘ a)
          ( modal-logic-implication-box'
            ( modal-logic-implication-dn a))))
```
