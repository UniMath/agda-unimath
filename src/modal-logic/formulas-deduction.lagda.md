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
open import modal-logic.formulas
open import modal-logic.logic-syntax
open import modal-logic.modal-logic-K
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
  (is-normal : modal-logic-K i ⊆ modal-logic axioms)
  where

  private
    contains-ax-k : ax-k i ⊆ modal-logic axioms
    contains-ax-k =
      transitive-leq-subtype
        ( ax-k i)
        ( modal-logic-K i)
        ( modal-logic axioms)
        is-normal
        ( K-contains-ax-k i)

    contains-ax-s : ax-s i ⊆ modal-logic axioms
    contains-ax-s =
      transitive-leq-subtype
        ( ax-s i)
        ( modal-logic-K i)
        ( modal-logic axioms)
        is-normal
        ( K-contains-ax-s i)

    contains-ax-n : ax-n i ⊆ modal-logic axioms
    contains-ax-n =
      transitive-leq-subtype
        ( ax-n i)
        ( modal-logic-K i)
        ( modal-logic axioms)
        is-normal
        ( K-contains-ax-n i)

    contains-ax-dn : ax-dn i ⊆ modal-logic axioms
    contains-ax-dn =
      transitive-leq-subtype
        ( ax-dn i)
        ( modal-logic-K i)
        ( modal-logic axioms)
        is-normal
        ( K-contains-ax-dn i)

  modal-logic-const :
    (a : formula i) {b : formula i} →
    is-in-subtype (modal-logic axioms) b →
    is-in-subtype (modal-logic axioms) (a →ₘ b)
  modal-logic-const a {b} b-in-logic =
    modal-logic-mp (contains-ax-k _ (b , a , refl)) (b-in-logic)

  modal-logic-transitivity :
    {a b c : formula i} →
    is-in-subtype (modal-logic axioms) (b →ₘ c) →
    is-in-subtype (modal-logic axioms) (a →ₘ b) →
    is-in-subtype (modal-logic axioms) (a →ₘ c)
  modal-logic-transitivity {a} {b} {c} bc ab =
    modal-logic-mp
      ( modal-logic-mp
        (contains-ax-s _ (a , b , c , refl))
        (modal-logic-const a bc))
      ( ab)

  modal-logic-implication-box' :
    {a b : formula i} →
    is-in-subtype (modal-logic axioms) (a →ₘ b) →
    is-in-subtype (modal-logic axioms) (□ a →ₘ □ b)
  modal-logic-implication-box' {a} {b} ab =
    modal-logic-mp (contains-ax-n _ (a , b , refl)) (modal-logic-nec ab)

  modal-logic-implication-box :
    {a b : formula i} →
    is-in-subtype (modal-logic axioms) (a →ₘ b) →
    is-in-subtype (modal-logic axioms) (□ a) →
    is-in-subtype (modal-logic axioms) (□ b)
  modal-logic-implication-box {a} {b} ab boxa =
    modal-logic-mp
      ( modal-logic-mp (contains-ax-n _ (a , b , refl)) (modal-logic-nec ab))
      ( boxa)

  modal-logic-implication-dn :
    (a : formula i) → is-in-subtype (modal-logic axioms) (a →ₘ ~~ a)
  modal-logic-implication-dn a =
    subset-double-modal-logic axioms
      ( a →ₘ (a →ₘ ⊥) →ₘ ⊥)
      ( weak-modal-logic-subset-modal-logic
        ( modal-logic axioms)
        ( a →ₘ (a →ₘ ⊥) →ₘ ⊥)
        ( forward-implication
          ( deduction-lemma
            ( modal-logic axioms)
            ( transitive-leq-subtype
              ( ax-k i)
              ( modal-logic axioms)
              ( weak-modal-logic (modal-logic axioms))
              ( axioms-subset-weak-modal-logic (modal-logic axioms))
              ( contains-ax-k))
            ( transitive-leq-subtype
              ( ax-s i)
              ( modal-logic axioms)
              ( weak-modal-logic (modal-logic axioms))
              ( axioms-subset-weak-modal-logic (modal-logic axioms))
              ( contains-ax-s))
            ( a)
            ( (a →ₘ ⊥) →ₘ ⊥))
          ( forward-implication
            ( deduction-lemma
              ( theory-add-formula a (modal-logic axioms))
              ( transitive-leq-subtype
                ( ax-k i)
                ( theory-add-formula a (modal-logic axioms))
                ( weak-modal-logic (theory-add-formula a (modal-logic axioms)))
                ( axioms-subset-weak-modal-logic
                  ( theory-add-formula a (modal-logic axioms)))
                ( transitive-leq-subtype
                  ( ax-k i)
                  ( modal-logic axioms)
                  ( theory-add-formula a (modal-logic axioms))
                  ( subtype-union-right
                    ( Id-formula-Prop a)
                    ( modal-logic axioms))
                  ( contains-ax-k)))
              ( transitive-leq-subtype
                ( ax-s i)
                ( theory-add-formula a (modal-logic axioms))
                ( weak-modal-logic (theory-add-formula a (modal-logic axioms)))
                ( axioms-subset-weak-modal-logic
                  ( theory-add-formula a (modal-logic axioms)))
                ( transitive-leq-subtype
                  ( ax-s i)
                  ( modal-logic axioms)
                  ( theory-add-formula a (modal-logic axioms))
                  ( subtype-union-right
                    ( Id-formula-Prop a)
                    ( modal-logic axioms))
                  ( contains-ax-s)))
              ( a →ₘ ⊥)
              ( ⊥))
            ( weak-modal-logic-mp
              ( weak-modal-logic-ax
                ( subtype-union-left
                  ( Id-formula-Prop (~ a))
                  ( theory-add-formula a (modal-logic axioms))
                  ( ~ a)
                  ( refl)))
              ( weak-modal-logic-ax
                ( subtype-union-right
                  ( Id-formula-Prop (~ a))
                  ( theory-add-formula a (modal-logic axioms))
                  ( a)
                  ( subtype-union-left
                    ( Id-formula-Prop a)
                    ( modal-logic axioms)
                    ( a)
                    ( refl))))))))

  modal-logic-diamond-negate :
    {a : formula i} →
    is-in-subtype (modal-logic axioms) (◇ ~ a) →
    is-in-subtype (modal-logic axioms) (~ □ a)
  modal-logic-diamond-negate {a} dia-a =
    modal-logic-transitivity
      ( dia-a)
      ( modal-logic-implication-box' (modal-logic-implication-dn a))

module _
  {l1 l2 : Level} (i : Set l1)
  (axioms : modal-theory l2 i)
  (is-normal : modal-logic-K i ⊆ weak-modal-logic axioms)
  where

  postulate
    weak-modal-logic-diamond-negate :
      {a : formula i} →
      is-in-subtype (weak-modal-logic axioms) (◇ ~ a) →
      is-in-subtype (weak-modal-logic axioms) (~ □ a)
```
