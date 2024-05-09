# L-complete theories

```agda
module modal-logic.l-complete-theories where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.inhabited-subtypes
open import foundation.inhabited-types
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.propositional-resizing
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.unions-subtypes
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.propositions
open import foundation-core.sets

open import lists.lists
open import lists.lists-subtypes

open import modal-logic.axioms
open import modal-logic.deduction
open import modal-logic.formulas
open import modal-logic.formulas-deduction
open import modal-logic.l-consistent-theories
open import modal-logic.modal-logic-k
open import modal-logic.weak-deduction

open import order-theory.chains-posets
open import order-theory.maximal-elements-posets
open import order-theory.posets
open import order-theory.subposets
open import order-theory.subtypes-leq-posets
open import order-theory.zorn
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 l2 : Level} {i : Set l1}
  (logic : modal-theory l2 i)
  where

  is-L-complete-theory-Prop :
    {l3 : Level} → L-consistent-theory logic l3 → Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-L-complete-theory-Prop {l3} =
    is-maximal-element-Poset-Prop (L-consistent-theories-Poset logic l3)

  is-L-complete-theory :
    {l3 : Level} → L-consistent-theory logic l3 → UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-L-complete-theory = type-Prop ∘ is-L-complete-theory-Prop

  L-complete-theory : (l3 : Level) → UU (l1 ⊔ l2 ⊔ lsuc l3)
  L-complete-theory l3 = type-subtype (is-L-complete-theory-Prop {l3})

  L-consistent-theory-L-complete-theory :
    {l3 : Level} → L-complete-theory l3 → L-consistent-theory logic l3
  L-consistent-theory-L-complete-theory =
    inclusion-subtype is-L-complete-theory-Prop

  is-L-complete-theory-L-consistent-theory :
    {l3 : Level} (theory : L-complete-theory l3) →
    is-L-complete-theory (L-consistent-theory-L-complete-theory theory)
  is-L-complete-theory-L-consistent-theory =
    is-in-subtype-inclusion-subtype is-L-complete-theory-Prop

  modal-theory-L-complete-theory :
    {l3 : Level} → L-complete-theory l3 → modal-theory l3 i
  modal-theory-L-complete-theory =
    modal-theory-L-consistent-theory logic ∘
      L-consistent-theory-L-complete-theory

  is-L-consistent-theory-modal-theory-L-complete-theory :
    {l3 : Level} (theory : L-complete-theory l3) →
    is-L-consistent-theory logic (modal-theory-L-complete-theory theory)
  is-L-consistent-theory-modal-theory-L-complete-theory =
    is-L-consistent-theory-modal-theory-L-consistent-theory logic ∘
      L-consistent-theory-L-complete-theory

  is-consistent-modal-theory-L-complete-theory :
    {l3 : Level} (theory : L-complete-theory l3) →
    is-consistent-modal-logic (modal-theory-L-complete-theory theory)
  is-consistent-modal-theory-L-complete-theory =
    is-consistent-modal-theory-L-consistent-theory logic ∘
      L-consistent-theory-L-complete-theory

  module _
    {l3 : Level}
    (((theory , is-cons) , is-comp) : L-complete-theory (l1 ⊔ l2 ⊔ l3))
    (theory' : modal-theory l3 i)
    where

    eq-is-L-consistent-union-L-complete :
      is-L-consistent-theory logic (theory' ∪ theory) →
      theory' ∪ theory ＝ theory
    eq-is-L-consistent-union-L-complete is-L-cons =
      ap
        ( modal-theory-L-consistent-theory logic)
        ( is-comp
          ( theory' ∪ theory , is-L-cons)
          ( subtype-union-right theory' theory))

  union-L-consistent :
    {l3 : Level} →
    L-consistent-theory logic l3 →
    L-consistent-theory logic (l1 ⊔ l2 ⊔ l3)
  pr1 (union-L-consistent (theory , is-cons)) =
    weak-modal-logic-closure (logic ∪ theory)
  pr2 (union-L-consistent (theory , is-cons)) bot-in-logic =
    is-cons
      ( transitive-leq-subtype
        ( weak-modal-logic-closure
          ( logic ∪ weak-modal-logic-closure (logic ∪ theory)))
        ( weak-modal-logic-closure (weak-modal-logic-closure (logic ∪ theory)))
        ( weak-modal-logic-closure (logic ∪ theory))
        ( is-weak-modal-logic-weak-modal-logic-closure)
        ( weak-modal-logic-closure-monotic
          ( subtype-union-both
            ( logic)
            ( weak-modal-logic-closure (logic ∪ theory))
            ( weak-modal-logic-closure (logic ∪ theory))
            ( transitive-leq-subtype
              ( logic)
              ( logic ∪ theory)
              ( weak-modal-logic-closure (logic ∪ theory))
              ( subset-axioms-weak-modal-logic-closure)
              ( subtype-union-left logic theory))
            ( refl-leq-subtype (weak-modal-logic-closure (logic ∪ theory)))))
        ( ⊥ₘ)
        ( bot-in-logic))

  module _
    (l3 : Level)
    (t@((theory , is-cons) , is-comp) : L-complete-theory (l1 ⊔ l2 ⊔ l3))
    where

    eq-union-L-consistent :
      weak-modal-logic-closure (logic ∪ theory) ＝ theory
    eq-union-L-consistent =
      ap
        ( modal-theory-L-consistent-theory logic)
        ( is-comp
          ( union-L-consistent (theory , is-cons))
          ( transitive-leq-subtype
            ( theory)
            ( logic ∪ theory)
            ( weak-modal-logic-closure (logic ∪ theory))
            ( subset-axioms-weak-modal-logic-closure)
            ( subtype-union-right logic theory)))

    subset-union-L-consistent :
      weak-modal-logic-closure (logic ∪ theory) ⊆ theory
    subset-union-L-consistent =
      inv-tr
        ( _⊆ theory)
        ( eq-union-L-consistent)
        ( refl-leq-subtype theory)

    subset-union-logic-L-complete-theory :
      logic ∪ theory ⊆ theory
    subset-union-logic-L-complete-theory =
      transitive-leq-subtype
        ( logic ∪ theory)
        ( modal-theory-L-consistent-theory logic
          ( union-L-consistent (theory , is-cons)))
        ( theory)
        ( subset-union-L-consistent)
        ( subset-axioms-weak-modal-logic-closure)

    subset-logic-L-complete-theory : logic ⊆ theory
    subset-logic-L-complete-theory =
      transitive-leq-subtype
        ( logic)
        ( logic ∪ theory)
        ( theory)
        ( subset-union-logic-L-complete-theory)
        ( subtype-union-left logic theory)

    is-weak-modal-logic-L-complete-theory : is-weak-modal-logic theory
    is-weak-modal-logic-L-complete-theory =
      transitive-leq-subtype
        ( weak-modal-logic-closure theory)
        ( modal-theory-L-consistent-theory logic
          ( union-L-consistent (theory , is-cons)))
        ( theory)
        ( subset-union-L-consistent)
        ( weak-modal-logic-closure-monotic (subtype-union-right logic theory))

  module _
    {l3 : Level}
    (t@((theory , is-cons) , is-comp) : L-complete-theory (l1 ⊔ l2 ⊔ l3))
    (theory' : modal-theory l3 i)
    where

    eq-is-consistent-union-L-complete :
      is-consistent-modal-logic (weak-modal-logic-closure (theory' ∪ theory)) →
      theory' ∪ theory ＝ theory
    eq-is-consistent-union-L-complete is-cons' =
      eq-is-L-consistent-union-L-complete t theory'
        ( is-consistent-modal-logic-antimonotic
          ( weak-modal-logic-closure (logic ∪ (theory' ∪ theory)))
          ( weak-modal-logic-closure (theory' ∪ theory))
          ( weak-modal-logic-closure-monotic
            ( subtype-union-both logic (theory' ∪ theory) (theory' ∪ theory)
              ( transitive-leq-subtype
                ( logic)
                ( theory)
                ( theory' ∪ theory)
                ( subtype-union-right theory' theory)
                ( subset-logic-L-complete-theory l3 t))
              ( refl-leq-subtype (theory' ∪ theory))))
          ( is-cons'))

  module _
    (t@((theory , is-cons) , is-comp) : L-complete-theory (l1 ⊔ l2))
    (contains-ax-k : ax-k i ⊆ logic)
    (contains-ax-s : ax-s i ⊆ logic)
    (contains-ax-dn : ax-dn i ⊆ logic)
    where

    private
      contains-ax-k' : ax-k i ⊆ theory
      contains-ax-k' =
        transitive-leq-subtype (ax-k i) logic theory
          ( subset-logic-L-complete-theory lzero t)
          ( contains-ax-k)

      contains-ax-s' : ax-s i ⊆ theory
      contains-ax-s' =
        transitive-leq-subtype (ax-s i) logic theory
          ( subset-logic-L-complete-theory lzero t)
          ( contains-ax-s)

      contains-ax-dn' : ax-dn i ⊆ theory
      contains-ax-dn' =
        transitive-leq-subtype (ax-dn i) logic theory
          ( subset-logic-L-complete-theory lzero t)
          ( contains-ax-dn)

    is-L-consistent-add-formula-not-in-logic :
      {a : modal-formula i} →
      ¬ (is-in-subtype theory a) →
      is-L-consistent-theory logic (theory-add-formula (¬ₘ a) theory)
    is-L-consistent-add-formula-not-in-logic {a} not-in-logic bot-in-logic =
      not-in-logic
        ( weak-modal-logic-mp
          ( is-weak-modal-logic-L-complete-theory lzero t)
          ( contains-ax-dn' (¬¬ₘ a →ₘ a) (a , refl))
          ( is-weak-modal-logic-L-complete-theory lzero t (¬¬ₘ a)
            ( forward-implication
              ( deduction-theorem
                ( theory)
                ( contains-ax-k')
                ( contains-ax-s')
                ( ¬ₘ a)
                ( ⊥ₘ))
              ( weak-modal-logic-closure-monotic
                ( subtype-union-both logic (theory-add-formula (¬ₘ a) theory)
                  ( theory-add-formula (¬ₘ a) theory)
                  ( transitive-leq-subtype
                    ( logic)
                    ( theory)
                    ( theory-add-formula (¬ₘ a) theory)
                    ( subset-add-formula (¬ₘ a) theory)
                    ( subset-logic-L-complete-theory lzero t))
                  ( refl-leq-subtype (theory-add-formula (¬ₘ a) theory)))
                ( ⊥ₘ)
                ( bot-in-logic)))))

    contains-negation-not-contains-formula-L-complete-theory :
      {a : modal-formula i} →
      ¬ (is-in-subtype theory a) →
      is-in-subtype theory (¬ₘ a)
    contains-negation-not-contains-formula-L-complete-theory {a} not-in-logic =
      tr
        ( λ t → is-in-subtype t (¬ₘ a))
        ( eq-is-L-consistent-union-L-complete t
          ( Id-formula-Prop (¬ₘ a))
          ( is-L-consistent-add-formula-not-in-logic not-in-logic))
        ( formula-in-add-formula (¬ₘ a) theory)

    module _
      (lem : LEM (l1 ⊔ l2))
      where

      is-disjuctive-L-complete-theory :
        is-disjuctive-modal-theory theory
      is-disjuctive-L-complete-theory a with lem (theory a)
      ... | inl a-in-logic = inl a-in-logic
      ... | inr a-not-in-logic =
        inr
          ( contains-negation-not-contains-formula-L-complete-theory
            ( a-not-in-logic))

      -- TODO: move from module
      lemma-box-diamond-L-complete :
        is-modal-logic logic →
        is-normal-modal-logic logic →
        (((theory' , _) , _) : L-complete-theory (l1 ⊔ l2)) →
        diamond-modal-theory theory ⊆ theory' →
        unbox-modal-theory theory' ⊆ theory
      lemma-box-diamond-L-complete is-logic is-normal x leq a box-a-in-x
        with is-disjuctive-L-complete-theory a
      ... | inl a-in-t = a-in-t
      ... | inr not-a-in-t =
        ex-falso
          ( is-consistent-modal-theory-L-complete-theory x
            ( weak-modal-logic-mp
              ( is-weak-modal-logic-L-complete-theory lzero x)
              { a = □ₘ a}
              ( weak-modal-logic-mp
                  ( is-weak-modal-logic-L-complete-theory lzero x)
                  { a = ◇ₘ ¬ₘ a}
                  ( subset-logic-L-complete-theory lzero x (◇ₘ ¬ₘ a →ₘ ¬ₘ □ₘ a)
                    ( modal-logic-diamond-negate-implication i logic is-normal
                      ( is-logic)))
                  ( leq (◇ₘ ¬ₘ a) (intro-exists (¬ₘ a) (not-a-in-t , refl))))
              ( box-a-in-x)))

  is-inhabited-L-complete-exists-complete-L-consistent-theory :
    {l3 : Level} →
    exists (L-consistent-theory logic l3) is-L-complete-theory-Prop →
    is-inhabited (L-complete-theory l3)
  is-inhabited-L-complete-exists-complete-L-consistent-theory {l3} =
    elim-exists
      ( is-inhabited-Prop (L-complete-theory l3))
      ( λ theory is-comp → unit-trunc-Prop (theory , is-comp))

  module _
    {l3 l4 : Level}
    (C : chain-Poset l4 (L-consistent-theories-Poset logic l3))
    where

    private
      P : Poset (l1 ⊔ l2 ⊔ lsuc l3) (l1 ⊔ l3)
      P = L-consistent-theories-Poset logic l3

      modal-theory-chain-element :
        type-chain-Poset P C → modal-theory l3 i
      modal-theory-chain-element =
        modal-theory-L-consistent-theory logic ∘
          type-Poset-type-chain-Poset P C

      L-union : type-chain-Poset P C → modal-theory (l1 ⊔ l2 ⊔ l3) i
      L-union x =
        weak-modal-logic-closure (logic ∪ modal-theory-chain-element x)

      theory-subset-L-union :
        (x : type-chain-Poset P C) → modal-theory-chain-element x ⊆ L-union x
      theory-subset-L-union x =
        transitive-leq-subtype
          ( modal-theory-chain-element x)
          ( logic ∪ modal-theory-chain-element x)
          ( L-union x)
          ( subset-axioms-weak-modal-logic-closure)
          ( subtype-union-right logic (modal-theory-chain-element x))

      leq-L-union :
        (x y : type-chain-Poset P C) →
        modal-theory-chain-element x ⊆ modal-theory-chain-element y →
        L-union x ⊆ L-union y
      leq-L-union x y leq =
        weak-modal-logic-closure-monotic
          ( subset-union-subset-right logic
            ( modal-theory-chain-element x)
            ( modal-theory-chain-element y)
            ( leq))

    chain-union-modal-theory :
      modal-theory (l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4) i
    chain-union-modal-theory a =
      ∃ (type-chain-Poset P C) (λ x → modal-theory-chain-element x a)

    is-inhabited-chain-is-inhabited-chain-union :
      is-inhabited-subtype (chain-union-modal-theory) →
      is-inhabited (type-chain-Poset P C)
    is-inhabited-chain-is-inhabited-chain-union =
      map-universal-property-trunc-Prop
        ( is-inhabited-Prop (type-chain-Poset P C))
        ( λ (x , x-in-union) →
          ( apply-universal-property-trunc-Prop
            ( x-in-union)
            ( is-inhabited-Prop (type-chain-Poset P C))
            ( λ (c , _) → unit-trunc-Prop c)))

    exists-chain-element-with-formula-Prop :
      (a : modal-formula i) → Prop (l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4)
    exists-chain-element-with-formula-Prop a =
      ∃ (type-chain-Poset P C)
        ( λ x →
          ( weak-modal-logic-closure (logic ∪ modal-theory-chain-element x) a))

    exists-chain-element-with-formula :
      (a : modal-formula i) → UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4)
    exists-chain-element-with-formula =
      type-Prop ∘ exists-chain-element-with-formula-Prop

    module _
      (contains-ax-k : ax-k i ⊆ logic)
      (contains-ax-s : ax-s i ⊆ logic)
      where

      private
        contains-ax-k' :
          {l5 : Level} (theory : modal-theory l5 i) → ax-k i ⊆ logic ∪ theory
        contains-ax-k' theory =
          transitive-leq-subtype (ax-k i) logic (logic ∪ theory)
            ( subtype-union-left logic theory)
            ( contains-ax-k)

        contains-ax-s' :
          {l5 : Level} (theory : modal-theory l5 i) → ax-s i ⊆ logic ∪ theory
        contains-ax-s' theory =
          transitive-leq-subtype (ax-s i) logic (logic ∪ theory)
            ( subtype-union-left logic theory)
            ( contains-ax-s)

        L-union-deduction-theorem :
          (l : list (modal-formula i)) →
          (h a : modal-formula i) →
          is-in-subtype
            ( weak-modal-logic-closure (logic ∪ list-subtype (cons h l))) a →
          is-in-subtype
            ( weak-modal-logic-closure (logic ∪ list-subtype l)) (h →ₘ a)
        L-union-deduction-theorem l h a in-logic =
          forward-implication
            ( deduction-theorem
              ( logic ∪ list-subtype l)
              ( contains-ax-k' (list-subtype l))
              ( contains-ax-s' (list-subtype l))
              ( h)
              ( a))
            ( weak-modal-logic-closure-monotic
              ( transitive-leq-subtype
                ( logic ∪ list-subtype (cons h l))
                ( logic ∪ theory-add-formula h (list-subtype l))
                ( theory-add-formula h (logic ∪ list-subtype l))
                ( theory-add-formula-union-right h logic (list-subtype l))
                ( subset-union-subset-right
                  ( logic)
                  ( list-subtype (cons h l))
                  ( theory-add-formula h (list-subtype l))
                  ( backward-subset-head-add h l)))
              ( a)
              ( in-logic))

      in-chain-in-chain-union-assumptions :
        is-inhabited (type-chain-Poset P C) →
        (l : list (modal-formula i)) →
        list-subtype l ⊆ chain-union-modal-theory →
        {a : modal-formula i} →
        is-in-subtype (weak-modal-logic-closure (logic ∪ list-subtype l)) a →
        exists-chain-element-with-formula a
      in-chain-in-chain-union-assumptions is-inh nil leq {a} in-logic =
        apply-universal-property-trunc-Prop
          ( is-inh)
          ( exists-chain-element-with-formula-Prop a)
          ( λ x →
            ( intro-exists x
              ( weak-modal-logic-closure-monotic
                ( subtype-union-both logic (list-subtype nil)
                  ( logic ∪ modal-theory-chain-element x)
                  ( subtype-union-left logic (modal-theory-chain-element x))
                  ( subset-list-subtype-nil
                    ( logic ∪ modal-theory-chain-element x)))
                ( a)
                ( in-logic))))
      in-chain-in-chain-union-assumptions is-inh (cons h l) leq {a} in-logic =
        apply-twice-universal-property-trunc-Prop
          ( leq h (head-in-list-subtype))
          ( in-chain-in-chain-union-assumptions is-inh l
            ( transitive-leq-subtype
              ( list-subtype l)
              ( list-subtype (cons h l))
              ( chain-union-modal-theory)
              ( leq)
              ( subset-tail-list-subtype))
            ( L-union-deduction-theorem l h a in-logic))
          ( exists-chain-element-with-formula-Prop a)
          ( λ (x , h-in-x) (y , ha-in-y) →
            ( elim-disjunction
              ( exists-chain-element-with-formula-Prop a)
              ( λ x-leq-y →
                ( intro-exists y
                  ( weak-modal-logic-closure-mp
                    ( ha-in-y)
                    ( leq-L-union x y x-leq-y h
                      ( theory-subset-L-union x h h-in-x)))))
              ( λ y-leq-x →
                ( intro-exists x
                  ( weak-modal-logic-closure-mp
                    ( leq-L-union y x y-leq-x (h →ₘ a) ha-in-y)
                    ( theory-subset-L-union x h h-in-x))))
              ( is-chain-Subposet-chain-Poset P C x y)))

      in-chain-in-list :
        (l : list (modal-formula i)) →
        list-subtype l ⊆ chain-union-modal-theory →
        {a : modal-formula i} →
        ¬ is-in-subtype (weak-modal-logic-closure logic) a →
        is-in-subtype (weak-modal-logic-closure (logic ∪ list-subtype l)) a →
        exists-chain-element-with-formula a
      in-chain-in-list l leq {a} not-in-logic in-union =
        in-chain-in-chain-union-assumptions
          ( is-inhabited-chain-is-inhabited-chain-union
            ( rec-coproduct
              ( map-is-inhabited (λ (x , in-list) → x , leq x in-list))
              ( λ not-inh →
                ( ex-falso
                  ( not-in-logic
                    ( weak-modal-logic-closure-monotic
                      ( subtype-union-both
                        ( logic)
                        ( list-subtype l)
                        ( logic)
                        ( refl-leq-subtype logic)
                        ( λ x in-list →
                          ( ex-falso
                            ( not-inh (unit-trunc-Prop (x , in-list))))))
                      ( a)
                      ( in-union)))))
              ( is-decidable-is-inhabited-list-subtype l)))
          ( l)
          ( leq)
          ( in-union)

      in-chain-in-chain-union :
        {a : modal-formula i} →
        ¬ is-in-subtype (weak-modal-logic-closure logic) a →
        is-in-subtype
          ( weak-modal-logic-closure (logic ∪ chain-union-modal-theory))
          ( a) →
        exists-chain-element-with-formula a
      in-chain-in-chain-union {a} not-in-logic =
        map-universal-property-trunc-Prop
          ( exists-chain-element-with-formula-Prop a)
          ( λ d →
            ( apply-universal-property-trunc-Prop
              ( lists-in-union-lists
                ( list-assumptions-weak-deduction d)
                ( logic)
                ( chain-union-modal-theory)
                ( subset-theory-list-assumptions-weak-deduction d))
              ( exists-chain-element-with-formula-Prop a)
              ( λ ((logic-l , theory-l) , leq-lists , leq-logic , leq-theory) →
                ( in-chain-in-list theory-l leq-theory not-in-logic
                  ( weak-modal-logic-closure-monotic
                    { ax₁ = list-subtype logic-l ∪ list-subtype theory-l}
                    ( subset-union-subset-left
                      ( list-subtype logic-l)
                      ( logic)
                      ( list-subtype theory-l)
                      ( leq-logic))
                    ( a)
                    ( weak-modal-logic-closure-monotic leq-lists a
                      ( is-in-weak-modal-logic-closure-weak-deduction
                        (is-assumptions-list-assumptions-weak-deduction
                          ( d)))))))))

      is-L-consistent-theory-chain-union-modal-theory :
        is-consistent-modal-logic (weak-modal-logic-closure logic) →
        is-L-consistent-theory logic chain-union-modal-theory
      is-L-consistent-theory-chain-union-modal-theory is-cons in-logic =
        apply-universal-property-trunc-Prop
          ( in-chain-in-chain-union is-cons in-logic)
          ( empty-Prop)
          ( λ (x , in-logic') →
            ( is-L-consistent-theory-modal-theory-L-consistent-theory
              ( logic)
              ( type-Poset-type-chain-Poset P C x)
              ( in-logic')))

  module _
    {l3 l4 : Level}
    (prop-resize : propositional-resizing l3 (l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4))
    where

    private
      P : Poset (l1 ⊔ l2 ⊔ lsuc l3) (l1 ⊔ l3)
      P = L-consistent-theories-Poset logic l3

    resized-chain-union-modal-theory : chain-Poset l4 P → modal-theory l3 i
    resized-chain-union-modal-theory C =
      resize prop-resize ∘ chain-union-modal-theory C

    equiv-resized-chain-union-modal-theory :
      (C : chain-Poset l4 P) →
      equiv-subtypes
        (resized-chain-union-modal-theory C)
        (chain-union-modal-theory C)
    equiv-resized-chain-union-modal-theory C a =
      is-equiv-resize prop-resize (chain-union-modal-theory C a)

    module _
      (contains-ax-k : ax-k i ⊆ logic)
      (contains-ax-s : ax-s i ⊆ logic)
      where

      is-L-consistent-resized-chain-union-modal-theory :
        (C : chain-Poset l4 P) →
        is-consistent-modal-logic (weak-modal-logic-closure logic) →
        is-L-consistent-theory logic (resized-chain-union-modal-theory C)
      is-L-consistent-resized-chain-union-modal-theory C is-cons =
        is-L-consistent-antimonotic logic
          ( resized-chain-union-modal-theory C)
          ( chain-union-modal-theory C)
          ( subset-equiv-subtypes
            ( resized-chain-union-modal-theory C)
            ( chain-union-modal-theory C)
            ( equiv-resized-chain-union-modal-theory C))
          ( is-L-consistent-theory-chain-union-modal-theory C
            ( contains-ax-k)
            ( contains-ax-s)
            ( is-cons))

      resized-chain-union-L-consistent-theory :
        (C : chain-Poset l4 P) →
        is-consistent-modal-logic (weak-modal-logic-closure logic) →
        L-consistent-theory logic l3
      pr1 (resized-chain-union-L-consistent-theory C is-cons) =
        resized-chain-union-modal-theory C
      pr2 (resized-chain-union-L-consistent-theory C is-cons) =
        is-L-consistent-resized-chain-union-modal-theory C is-cons

      union-is-chain-upper-bound :
        (C : chain-Poset l4 P) →
        (is-cons : is-consistent-modal-logic (weak-modal-logic-closure logic)) →
        is-chain-upper-bound P C
          ( resized-chain-union-L-consistent-theory C is-cons)
      union-is-chain-upper-bound C _ x =
        transitive-leq-subtype
          ( modal-theory-L-consistent-theory logic
            ( type-Poset-type-chain-Poset
              ( L-consistent-theories-Poset logic l3)
              ( C)
              ( x)))
          ( chain-union-modal-theory C)
          ( resized-chain-union-modal-theory C)
          ( inv-subset-equiv-subtypes
            ( resized-chain-union-modal-theory C)
            ( chain-union-modal-theory C)
            ( equiv-resized-chain-union-modal-theory C))
          ( λ a in-theory → intro-exists x in-theory)

      extend-L-consistent-theory :
        Zorn (l1 ⊔ l2 ⊔ lsuc l3) (l1 ⊔ l3) l4 →
        is-inhabited (L-consistent-theory logic l3) →
        is-inhabited (L-complete-theory l3)
      extend-L-consistent-theory zorn is-inh =
        map-universal-property-trunc-Prop
          ( is-inhabited-Prop (L-complete-theory l3))
          ( λ theory →
            ( zorn
              ( L-consistent-theories-Poset logic l3)
              ( λ C →
                ( intro-exists
                  ( resized-chain-union-L-consistent-theory C
                    ( is-consistent-closure-logic-L-consistent-theory logic
                      ( theory)))
                  ( union-is-chain-upper-bound C
                    ( is-consistent-closure-logic-L-consistent-theory logic
                      ( theory)))))))
          ( is-inh)

  module _
    {l3 : Level}
    (prop-resize : propositional-resizing (l1 ⊔ l2) (lsuc l1 ⊔ lsuc l2 ⊔ l3))
    (zorn : Zorn (lsuc l1 ⊔ lsuc l2) (l1 ⊔ l2) l3)
    (is-logic : is-weak-modal-logic logic)
    (is-cons : is-consistent-modal-logic logic)
    (contains-ax-k : ax-k i ⊆ logic)
    (contains-ax-s : ax-s i ⊆ logic)
    where

    is-inhabited-L-complete-theory :
      is-inhabited (L-complete-theory (l1 ⊔ l2))
    is-inhabited-L-complete-theory =
      extend-L-consistent-theory prop-resize contains-ax-k contains-ax-s zorn
        ( map-is-inhabited
          ( λ (t , t-is-cons) →
            ( pair
              ( raise-subtype l1 t)
              ( is-L-consistent-antimonotic logic (raise-subtype l1 t) t
                ( inv-subset-equiv-subtypes t (raise-subtype l1 t)
                  ( compute-raise-subtype l1 t))
                ( t-is-cons))))
          ( is-inhabited-L-consistent-theory logic is-logic is-cons))

module _
  {l1 : Level} {i : Set l1}
  {l2 l3 : Level}
  (logic₁ : modal-theory l2 i)
  (logic₂ : modal-theory l3 i)
  (theory : modal-theory (l1 ⊔ l2 ⊔ l3) i)
  (is-cons₁ : is-L-consistent-theory logic₁ theory)
  (is-cons₂ : is-L-consistent-theory logic₂ theory)
  where

  universal-L-complete-theory :
    is-L-complete-theory logic₁ (theory , is-cons₁) →
    is-L-complete-theory logic₂ (theory , is-cons₂)
  universal-L-complete-theory is-comp (theory' , is-cons') leq =
    eq-pair-Σ
      ( equational-proof)
      ( eq-is-prop
        ( is-prop-type-Prop (is-L-consistent-theory-Prop logic₂ theory)))
    where
    complete-theory : L-complete-theory logic₁ (l1 ⊔ l2 ⊔ l3)
    complete-theory = (theory , is-cons₁) , is-comp

    equational-proof : theory' ＝ theory
    equational-proof =
      equational-reasoning
      theory'
      ＝ theory' ∪ theory
        by inv (eq-union-subset-right theory' theory leq)
      ＝ theory
        by eq-is-consistent-union-L-complete logic₁ complete-theory theory'
          ( is-consistent-modal-logic-antimonotic
            ( weak-modal-logic-closure (theory' ∪ theory))
            ( weak-modal-logic-closure theory')
            ( weak-modal-logic-closure-monotic
              ( subtype-union-both theory' theory theory'
                ( refl-leq-subtype theory')
                ( leq)))
            ( is-consistent-closure-L-consistent-theory logic₂
              ( theory' , is-cons')))
```
