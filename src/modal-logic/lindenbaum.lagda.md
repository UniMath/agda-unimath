# Lindenbaum's lemma

```agda
module modal-logic.lindenbaum where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.propositional-resizing
open import foundation.propositional-truncations
open import foundation.unions-subtypes
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtypes

open import modal-logic.axioms
open import modal-logic.deduction
open import modal-logic.l-complete-theories
open import modal-logic.l-consistent-theories
open import modal-logic.weak-deduction

open import order-theory.zorn
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 l2 l3 : Level} {i : Set l1}
  (logic : modal-theory l2 i)
  (contains-ax-k : ax-k i ⊆ logic)
  (contains-ax-s : ax-s i ⊆ logic)
  (zorn : Zorn (lsuc (l1 ⊔ l2 ⊔ l3)) (l1 ⊔ l2 ⊔ l3) l3)
  (prop-resize : propositional-resizing (l1 ⊔ l2 ⊔ l3) (lsuc (l1 ⊔ l2 ⊔ l3)))
  (x@(theory , is-cons) : L-consistent-theory logic (l1 ⊔ l2 ⊔ l3))
  where

  lindenbaum :
    exists (L-complete-theory logic (l1 ⊔ l2 ⊔ l3))
      ( λ y →
        ( leq-prop-subtype
          ( modal-theory-L-consistent-theory logic x)
          ( modal-theory-L-complete-theory logic y)))
  lindenbaum =
    apply-universal-property-trunc-Prop
      ( extend-L-consistent-theory L prop-resize contains-ax-k' contains-ax-s'
        ( zorn)
        ( is-inhabited-L-consistent-theory L
          ( is-weak-modal-logic-weak-modal-logic-closure)
          ( is-cons)))
      ( ∃ (L-complete-theory logic (l1 ⊔ l2 ⊔ l3))
        ( λ y →
          ( leq-prop-subtype
            ( modal-theory-L-consistent-theory logic x)
            ( modal-theory-L-complete-theory logic y))))
      ( λ y →
        ( intro-exists
          ( result-L-complete y)
          ( subset-theory-transofrm-L-complete y)))
    where
    L : modal-theory (l1 ⊔ l2 ⊔ l3) i
    L = weak-modal-logic-closure (logic ∪ theory)

    subset-logic-L : logic ⊆ L
    subset-logic-L =
      transitive-leq-subtype
        ( logic)
        ( logic ∪ theory)
        ( weak-modal-logic-closure (logic ∪ theory))
        ( subset-axioms-weak-modal-logic-closure)
        ( subtype-union-left logic theory)

    contains-ax-k' : ax-k i ⊆ L
    contains-ax-k' =
      transitive-leq-subtype (ax-k i) logic L subset-logic-L contains-ax-k

    contains-ax-s' : ax-s i ⊆ L
    contains-ax-s' =
      transitive-leq-subtype (ax-s i) logic L subset-logic-L contains-ax-s

    is-L-consistent-result :
      (y : L-complete-theory L (l1 ⊔ l2 ⊔ l3)) →
      is-L-consistent-theory logic (modal-theory-L-complete-theory L y)
    is-L-consistent-result y =
      is-L-consistent-antimonotic-logic
        ( logic)
        ( weak-modal-logic-closure (logic ∪ theory))
        ( modal-theory-L-complete-theory L y)
        ( subset-logic-L)
        ( is-L-consistent-theory-modal-theory-L-complete-theory L y)

    result-L-consistent :
      L-complete-theory L (l1 ⊔ l2 ⊔ l3) →
      L-consistent-theory logic (l1 ⊔ l2 ⊔ l3)
    pr1 (result-L-consistent y) = modal-theory-L-complete-theory L y
    pr2 (result-L-consistent y) = is-L-consistent-result y

    is-L-complete-result :
      (y : L-complete-theory L (l1 ⊔ l2 ⊔ l3)) →
      is-L-complete-theory logic (result-L-consistent y)
    is-L-complete-result y =
      universal-L-complete-theory L logic
        ( modal-theory-L-complete-theory L y)
        ( is-L-consistent-theory-modal-theory-L-complete-theory L y)
        ( is-L-consistent-result y)
        ( is-L-complete-theory-L-consistent-theory L y)

    result-L-complete :
      L-complete-theory L (l1 ⊔ l2 ⊔ l3) →
      L-complete-theory logic (l1 ⊔ l2 ⊔ l3)
    pr1 (pr1 (result-L-complete y)) = modal-theory-L-complete-theory L y
    pr2 (pr1 (result-L-complete y)) = is-L-consistent-result y
    pr2 (result-L-complete y) = is-L-complete-result y

    subset-theory-transofrm-L-complete :
      (y : L-complete-theory L (l1 ⊔ l2 ⊔ l3)) →
      theory ⊆ modal-theory-L-complete-theory logic (result-L-complete y)
    subset-theory-transofrm-L-complete y =
      ( transitive-leq-subtype theory L
        ( modal-theory-L-complete-theory L y)
        ( subset-logic-L-complete-theory L l3 y)
        ( transitive-leq-subtype
          ( theory)
          ( logic ∪ theory)
          ( L)
          ( subset-axioms-weak-modal-logic-closure)
          ( subtype-union-right logic theory)))
```
