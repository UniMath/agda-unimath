# Canonical model theorem

```agda
module modal-logic.canonical-model-theorem where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-resizing
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.unions-subtypes
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.propositions

open import lists.lists
open import lists.lists-subtypes
open import lists.reversing-lists

open import modal-logic.axioms
open import modal-logic.completeness
open import modal-logic.deduction
open import modal-logic.formulas
open import modal-logic.kripke-semantics
open import modal-logic.l-complete-theories
open import modal-logic.l-consistent-theories
open import modal-logic.lindenbaum
open import modal-logic.modal-logic-k
open import modal-logic.weak-deduction

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
  (is-logic : is-modal-logic logic)
  (is-cons : is-consistent-modal-logic logic)
  (is-normal : is-normal-modal-logic logic)
  (zorn : Zorn (lsuc l1 ⊔ lsuc l2) (l1 ⊔ l2) l2)
  (prop-resize : propositional-resizing (l1 ⊔ l2) (lsuc (l1 ⊔ l2)))
  where

  private
    is-weak-logic : is-weak-modal-logic logic
    is-weak-logic = is-weak-modal-logic-is-modal-logic is-logic

    contains-ax-k : ax-k i ⊆ logic
    contains-ax-k =
      transitive-leq-subtype (ax-k i) (modal-logic-K i) logic
        ( is-normal)
        ( K-contains-ax-k i)

    contains-ax-s : ax-s i ⊆ logic
    contains-ax-s =
      transitive-leq-subtype (ax-s i) (modal-logic-K i) logic
        ( is-normal)
        ( K-contains-ax-s i)

    contains-ax-n : ax-n i ⊆ logic
    contains-ax-n =
      transitive-leq-subtype (ax-n i) (modal-logic-K i) logic
        ( is-normal)
        ( K-contains-ax-n i)

    contains-ax-dn : ax-dn i ⊆ logic
    contains-ax-dn =
      transitive-leq-subtype (ax-dn i) (modal-logic-K i) logic
        ( is-normal)
        ( K-contains-ax-dn i)

  canonical-kripke-model :
    kripke-model (lsuc l1 ⊔ lsuc l2) (l1 ⊔ l2) i (l1 ⊔ l2)
  pr1 (pr1 canonical-kripke-model) =
    L-complete-theory logic (l1 ⊔ l2)
  pr2 (pr1 canonical-kripke-model) =
    is-inhabited-L-complete-theory
      ( logic)
      ( prop-resize)
      ( zorn)
      ( is-weak-logic)
      ( is-cons)
      ( contains-ax-k)
      ( contains-ax-s)
  pr1 (pr2 canonical-kripke-model) x y =
    Π-Prop
      ( modal-formula i)
      ( λ a →
        ( modal-theory-L-complete-theory logic x (□ₘ a) ⇒
            modal-theory-L-complete-theory logic y a))
  pr2 (pr2 canonical-kripke-model) n x =
    modal-theory-L-complete-theory logic x (varₘ n)

  module _
    (lem : LEM (l1 ⊔ l2))
    where

    module _
      (x@((theory , is-cons) , is-comp) : L-complete-theory logic (l1 ⊔ l2))
      where

      private
        contains-ax-k' : ax-k i ⊆ theory
        contains-ax-k' =
          transitive-leq-subtype (ax-k i) logic theory
            ( subset-logic-L-complete-theory logic lzero x)
            ( contains-ax-k)

        contains-ax-s' : ax-s i ⊆ theory
        contains-ax-s' =
          transitive-leq-subtype (ax-s i) logic theory
            ( subset-logic-L-complete-theory logic lzero x)
            ( contains-ax-s)

        contains-ax-dn' : ax-dn i ⊆ theory
        contains-ax-dn' =
          transitive-leq-subtype (ax-dn i) logic theory
            ( subset-logic-L-complete-theory logic lzero x)
            ( contains-ax-dn)

        contains-ax-n' : ax-n i ⊆ theory
        contains-ax-n' =
          transitive-leq-subtype (ax-n i) logic theory
            ( subset-logic-L-complete-theory logic lzero x)
            ( contains-ax-n)

        contains-ax-k-union :
          {l : Level} (t : modal-theory l i) → ax-k i ⊆ logic ∪ t
        contains-ax-k-union t =
          transitive-leq-subtype (ax-k i) logic (logic ∪ t)
            ( subtype-union-left logic t)
            ( contains-ax-k)

        contains-ax-s-union :
          {l : Level} (t : modal-theory l i) → ax-s i ⊆ logic ∪ t
        contains-ax-s-union t =
          transitive-leq-subtype (ax-s i) logic (logic ∪ t)
            ( subtype-union-left logic t)
            ( contains-ax-s)

        is-disjuctive-theory : is-disjuctive-modal-theory theory
        is-disjuctive-theory =
          is-disjuctive-L-complete-theory logic x
            ( contains-ax-k)
            ( contains-ax-s)
            ( contains-ax-dn)
            ( lem)

      L-complete-theory-implication :
        {a b : modal-formula i} →
        (is-in-subtype theory a → is-in-subtype theory b) →
        is-in-subtype theory (a →ₘ b)
      L-complete-theory-implication {a} {b} f with is-disjuctive-theory a
      ... | inl a-in-logic =
        is-weak-modal-logic-L-complete-theory logic lzero x (a →ₘ b)
          ( forward-implication
            ( deduction-theorem theory contains-ax-k' contains-ax-s' a b)
            ( weak-modal-logic-closure-monotic
              { ax₁ = theory}
              { ax₂ = theory-add-formula a theory}
              ( subset-add-formula a theory)
              ( b)
              ( weak-modal-logic-closure-ax (f a-in-logic))))
      ... | inr not-a-in-logic =
        is-weak-modal-logic-L-complete-theory logic lzero x (a →ₘ b)
          ( forward-implication
            ( deduction-theorem theory contains-ax-k' contains-ax-s' a b)
            ( logic-ex-falso
              ( theory-add-formula a theory)
              ( transitive-subset-add-formula a theory (ax-k i) contains-ax-k')
              ( transitive-subset-add-formula a theory (ax-s i) contains-ax-s')
              ( transitive-subset-add-formula a theory
                ( ax-dn i)
                ( contains-ax-dn'))
              ( a)
              ( b)
              ( weak-modal-logic-closure-ax (formula-in-add-formula a theory))
              ( weak-modal-logic-closure-monotic
                { ax₁ = theory}
                { ax₂ = theory-add-formula a theory}
                ( subset-add-formula a theory)
                ( ¬ₘ a)
                ( weak-modal-logic-closure-ax not-a-in-logic))))

      L-complete-theory-box :
        {a : modal-formula i} →
        ( (y : L-complete-theory logic (l1 ⊔ l2)) →
          relation-kripke-model i canonical-kripke-model x y →
          is-in-subtype (modal-theory-L-complete-theory logic y) a) →
        is-in-subtype theory (□ₘ a)
      L-complete-theory-box {a} f with is-disjuctive-theory (□ₘ a)
      ... | inl box-a-in-logic = box-a-in-logic
      ... | inr not-box-a-in-logic =
        ex-falso
          ( apply-universal-property-trunc-Prop
            ( lindenbaum logic contains-ax-k contains-ax-s zorn prop-resize
              ( y , is-L-consistent-y))
            ( empty-Prop)
            ( λ (w , y-leq-w) →
              ( is-consistent-modal-theory-L-complete-theory logic w
                ( weak-modal-logic-mp
                  ( is-weak-modal-logic-L-complete-theory logic lzero w)
                  ( y-leq-w (¬ₘ a)
                    ( formula-in-add-formula
                      ( ¬ₘ a)
                      ( unbox-modal-theory theory)))
                  ( f w (λ b → y-leq-w b ∘ y-contains-unbox))))))
        where
        y : modal-theory (l1 ⊔ l2) i
        y = theory-add-formula (¬ₘ a) (unbox-modal-theory theory)

        y-contains-unbox :
          {b : modal-formula i} →
          is-in-subtype theory (□ₘ b) →
          is-in-subtype y b
        y-contains-unbox {b} =
          subset-add-formula (¬ₘ a) (unbox-modal-theory theory) b

        list-to-implications :
          modal-formula i → (l : list (modal-formula i)) → modal-formula i
        list-to-implications f nil = f
        list-to-implications f (cons g l) = list-to-implications (g →ₘ f) l

        list-to-implications-rev :
          modal-formula i → (l : list (modal-formula i)) → modal-formula i
        list-to-implications-rev f nil = f
        list-to-implications-rev f (cons g l) =
          g →ₘ list-to-implications-rev f l

        list-to-implication-rev-snoc :
          (f g : modal-formula i) (l : list (modal-formula i)) →
          list-to-implications f (snoc l g) ＝ g →ₘ list-to-implications f l
        list-to-implication-rev-snoc f g nil = refl
        list-to-implication-rev-snoc f g (cons h l) =
          list-to-implication-rev-snoc (h →ₘ f) g l

        eq-reverse-list-to-implications :
          (f : modal-formula i) (l : list (modal-formula i)) →
          list-to-implications f (reverse-list l) ＝ list-to-implications-rev f l
        eq-reverse-list-to-implications f nil = refl
        eq-reverse-list-to-implications f (cons g l) =
          ( list-to-implication-rev-snoc f g (reverse-list l)) ∙
          ( ap (λ x → g →ₘ x) (eq-reverse-list-to-implications f l))

        move-assumptions-right :
          (f : modal-formula i) (l : list (modal-formula i)) →
          is-in-subtype (weak-modal-logic-closure (logic ∪ list-subtype l)) f →
          is-in-subtype
            ( weak-modal-logic-closure logic)
            ( list-to-implications f l)
        move-assumptions-right f nil =
          weak-modal-logic-closure-monotic
            ( subtype-union-both
              ( logic)
              ( list-subtype nil)
              ( logic)
              ( refl-leq-subtype logic)
              ( subset-list-subtype-nil logic))
            ( f)
        move-assumptions-right f (cons c l) in-logic =
          move-assumptions-right (c →ₘ f) l
            ( forward-implication
              ( deduction-theorem
                ( logic ∪ list-subtype l)
                ( contains-ax-k-union (list-subtype l))
                ( contains-ax-s-union (list-subtype l))
                ( c)
                ( f))
              ( weak-modal-logic-closure-monotic
                ( transitive-leq-subtype
                  ( logic ∪ list-subtype (cons c l))
                  ( logic ∪ theory-add-formula c (list-subtype l))
                  ( theory-add-formula c (logic ∪ list-subtype l))
                  ( theory-add-formula-union-right c logic (list-subtype l))
                  ( subset-union-subset-right logic
                    ( list-subtype (cons c l))
                    ( theory-add-formula c (list-subtype l))
                    ( subset-list-subtype-cons
                      ( theory-add-formula c (list-subtype l))
                      ( formula-in-add-formula c (list-subtype l))
                      ( subset-add-formula c (list-subtype l)))))
                ( f)
                ( in-logic)))

        α :
          (l : list (modal-formula i)) →
          list-subtype l ⊆ unbox-modal-theory theory →
          is-in-subtype theory (□ₘ (list-to-implications-rev a l)) →
          is-in-subtype theory (□ₘ a)
        α nil sub in-logic = in-logic
        α (cons c l) sub in-logic =
          α l
            ( transitive-leq-subtype
              ( list-subtype l)
              ( list-subtype (cons c l))
              ( unbox-modal-theory theory)
              ( sub)
              ( subset-tail-list-subtype))
            ( weak-modal-logic-mp
              ( is-weak-modal-logic-L-complete-theory logic lzero x)
              { a = □ₘ c}
              { b = □ₘ list-to-implications-rev a l}
              ( weak-modal-logic-mp
                ( is-weak-modal-logic-L-complete-theory logic lzero x)
                { a = □ₘ (c →ₘ list-to-implications-rev a l)}
                { b = □ₘ c →ₘ □ₘ (list-to-implications-rev a l)}
                ( contains-ax-n' _ (c , list-to-implications-rev a l , refl))
                ( in-logic))
              ( sub c head-in-list-subtype))

        β :
          (l : list (modal-formula i)) →
          list-subtype l ⊆ unbox-modal-theory theory →
          is-in-subtype (weak-modal-logic-closure (logic ∪ list-subtype l)) a →
          is-in-subtype theory (□ₘ a)
        β l sub in-logic =
          α l sub
            ( subset-logic-L-complete-theory logic lzero x
              ( □ₘ list-to-implications-rev a l)
              ( modal-logic-nec is-logic
                ( tr
                  ( is-in-subtype logic)
                  ( eq-reverse-list-to-implications a l)
                  ( is-weak-logic
                    ( list-to-implications a (reverse-list l))
                    ( move-assumptions-right a (reverse-list l)
                      ( weak-modal-logic-closure-monotic
                        ( subset-union-subset-right logic
                          ( list-subtype l)
                          ( list-subtype (reverse-list l))
                          ( subset-list-subtype-reverse-list l))
                        ( a)
                        ( in-logic)))))))

        γ :
          (l : list (modal-formula i)) →
          list-subtype l ⊆ unbox-modal-theory theory →
          is-contradictory-modal-logic
            ( weak-modal-logic-closure
              ( theory-add-formula (¬ₘ a) (logic ∪ list-subtype l))) →
          is-in-subtype theory (□ₘ a)
        γ l sub is-cont =
          β l sub
            ( weak-modal-logic-closure-mp {a = ¬¬ₘ a} {b = a}
              ( weak-modal-logic-closure-ax
                ( subtype-union-left logic (list-subtype l) (¬¬ₘ a →ₘ a)
                  ( contains-ax-dn (¬¬ₘ a →ₘ a) (a , refl))))
              ( forward-implication
                ( deduction-theorem
                  ( logic ∪ list-subtype l)
                  ( contains-ax-k-union (list-subtype l))
                  ( contains-ax-s-union (list-subtype l))
                  ( ¬ₘ a)
                  ( ⊥ₘ))
                ( is-cont)))

        δ :
          (l : list (modal-formula i)) →
          list-subtype l ⊆ unbox-modal-theory theory →
          is-contradictory-modal-logic
            ( weak-modal-logic-closure
              ( logic ∪ (theory-add-formula (¬ₘ a) (list-subtype l)))) →
          is-in-subtype theory (□ₘ a)
        δ l sub is-cont =
          γ l sub
            ( is-contradictory-modal-logic-monotic
              ( weak-modal-logic-closure
                ( logic ∪ theory-add-formula (¬ₘ a) (list-subtype l)))
              ( weak-modal-logic-closure
                ( theory-add-formula (¬ₘ a) (logic ∪ list-subtype l)))
              ( weak-modal-logic-closure-monotic
                ( theory-add-formula-union-right (¬ₘ a) logic (list-subtype l)))
              ( is-cont))

        ε :
          (l : list (modal-formula i)) →
          list-subtype l ⊆ logic ∪ y →
          is-contradictory-modal-logic
            ( weak-modal-logic-closure (list-subtype l)) →
          is-in-subtype theory (□ₘ a)
        ε l sub is-cont =
          apply-universal-property-trunc-Prop
            ( lists-in-union-lists l logic y sub)
            ( theory (□ₘ a))
            ( λ ((l-ax , l-y) , sub-union , l-ax-sub-logic , l-y-sub-y) →
              ( apply-universal-property-trunc-Prop
                ( lists-in-union-lists l-y
                  ( Id-modal-formula-Prop (¬ₘ a))
                  ( unbox-modal-theory theory)
                  ( l-y-sub-y))
                ( theory (□ₘ a))
                ( λ ((l-not-a , l-box) , sub-union' , l-not-a-sub , l-box-sub) →
                  ( δ
                    ( l-box)
                    ( l-box-sub)
                    ( is-contradictory-modal-logic-monotic
                      ( weak-modal-logic-closure (list-subtype l))
                      ( weak-modal-logic-closure
                        ( logic ∪
                            theory-add-formula (¬ₘ a) (list-subtype l-box)))
                      ( weak-modal-logic-closure-monotic
                        ( transitive-leq-subtype
                          ( list-subtype l)
                          ( list-subtype l-ax ∪ list-subtype l-y)
                          ( logic ∪
                              theory-add-formula (¬ₘ a) (list-subtype l-box))
                          ( subset-union-subsets
                            ( list-subtype l-ax)
                            ( list-subtype l-y)
                            ( logic)
                            ( theory-add-formula (¬ₘ a) (list-subtype l-box))
                            ( l-ax-sub-logic)
                            ( transitive-leq-subtype
                              ( list-subtype l-y)
                              ( list-subtype l-not-a ∪ list-subtype l-box)
                              ( theory-add-formula (¬ₘ a) (list-subtype l-box))
                              ( subtype-union-both
                                ( list-subtype l-not-a)
                                ( list-subtype l-box)
                                ( theory-add-formula
                                  ( ¬ₘ a)
                                  ( list-subtype l-box))
                                ( transitive-leq-subtype
                                  ( list-subtype l-not-a)
                                  ( Id-modal-formula-Prop (¬ₘ a))
                                  ( theory-add-formula (¬ₘ a)
                                    ( list-subtype l-box))
                                  ( subtype-union-left
                                    ( Id-modal-formula-Prop (¬ₘ a))
                                    ( list-subtype l-box))
                                  ( l-not-a-sub))
                                ( subset-add-formula
                                  ( ¬ₘ a)
                                  ( list-subtype l-box)))
                              ( sub-union')))
                          ( sub-union)))
                      ( is-cont))))))

        is-L-consistent-y : is-L-consistent-theory logic y
        is-L-consistent-y =
          map-universal-property-trunc-Prop
            ( empty-Prop)
            ( λ d-bot →
              ( is-consistent-modal-theory-L-complete-theory logic x
                ( weak-modal-logic-mp
                  ( is-weak-modal-logic-L-complete-theory logic lzero x)
                  ( not-box-a-in-logic)
                  ( ε
                    ( list-assumptions-weak-deduction d-bot)
                    ( subset-theory-list-assumptions-weak-deduction d-bot)
                    ( is-in-weak-modal-logic-closure-weak-deduction
                      ( is-assumptions-list-assumptions-weak-deduction
                        ( d-bot)))))))

    canonical-model-theorem-pointwise :
      (a : modal-formula i)
      (x : L-complete-theory logic (l1 ⊔ l2)) →
      type-iff-Prop
        ( modal-theory-L-complete-theory logic x a)
        ( (canonical-kripke-model , x) ⊨ₘ a)
    pr1 (canonical-model-theorem-pointwise (varₘ n) x) = map-raise
    pr1 (canonical-model-theorem-pointwise ⊥ₘ x) =
      map-raise ∘ is-consistent-modal-theory-L-complete-theory logic x
    pr1 (canonical-model-theorem-pointwise (a →ₘ b) x) in-logic f =
      forward-implication
        ( canonical-model-theorem-pointwise b x)
        ( weak-modal-logic-mp
          ( is-weak-modal-logic-L-complete-theory logic lzero x)
          ( in-logic)
          ( backward-implication (canonical-model-theorem-pointwise a x) f))
    pr1 (canonical-model-theorem-pointwise (□ₘ a) x) in-logic y xRy =
      forward-implication
        ( canonical-model-theorem-pointwise a y)
        ( xRy a in-logic)
    pr2 (canonical-model-theorem-pointwise (varₘ n) x) = map-inv-raise
    pr2 (canonical-model-theorem-pointwise ⊥ₘ x) (map-raise ())
    pr2 (canonical-model-theorem-pointwise (a →ₘ b) x) f =
      L-complete-theory-implication x
        ( λ in-x →
          ( backward-implication
            ( canonical-model-theorem-pointwise b x)
            ( f
              ( forward-implication
                ( canonical-model-theorem-pointwise a x)
                ( in-x)))))
    pr2 (canonical-model-theorem-pointwise (□ₘ a) x) f =
      L-complete-theory-box x
        ( λ y xRy →
          ( backward-implication
            ( canonical-model-theorem-pointwise a y)
            ( f y xRy)))

    canonical-model-theorem :
      (a : modal-formula i) →
      type-iff-Prop (logic a) (canonical-kripke-model ⊨Mₘ a)
    pr1 (canonical-model-theorem a) in-logic x =
      forward-implication
        ( canonical-model-theorem-pointwise a x)
        ( subset-logic-L-complete-theory logic lzero x a in-logic)
    pr2 (canonical-model-theorem a) =
      contraposition (lower-LEM l1 lem) (logic a)
        ( λ na f →
          ( apply-universal-property-trunc-Prop
            ( lindenbaum logic contains-ax-k contains-ax-s zorn prop-resize
              ( x , is-L-consistent-x na))
            ( empty-Prop)
            ( λ (w , leq) →
              ( is-consistent-modal-theory-L-complete-theory logic w
                ( weak-modal-logic-mp
                  ( is-weak-modal-logic-L-complete-theory logic lzero w)
                  ( leq (¬ₘ a) not-a-in-x)
                  ( backward-implication
                    ( canonical-model-theorem-pointwise a w)
                    ( f w)))))))
      where
      x : modal-theory (l1 ⊔ l2) i
      x = raise-subtype l2 (Id-modal-formula-Prop (¬ₘ a))

      not-a-in-x : is-in-subtype x ( ¬ₘ a)
      not-a-in-x =
        subset-equiv-subtypes (Id-modal-formula-Prop (¬ₘ a)) x
          ( compute-raise-subtype l2 (Id-modal-formula-Prop (¬ₘ a)))
          ( ¬ₘ a)
          ( refl)

      is-L-consistent-x :
        ¬ (is-in-subtype logic a) → is-L-consistent-theory logic x
      is-L-consistent-x a-not-in-logic bot-in-logic =
        a-not-in-logic
          ( modal-logic-mp is-logic
            {a = ¬¬ₘ a}
            {b = a}
            ( contains-ax-dn (¬¬ₘ a →ₘ a) (a , refl))
            ( is-logic (¬¬ₘ a)
              ( subset-weak-modal-logic-closure-modal-logic-closure (¬¬ₘ a)
                ( forward-implication
                  ( deduction-theorem logic contains-ax-k contains-ax-s
                    ( ¬ₘ a)
                    ( ⊥ₘ))
                  ( weak-modal-logic-closure-monotic
                    ( subtype-union-both logic x
                      ( theory-add-formula (¬ₘ a) logic)
                      ( subtype-union-right
                        ( Id-modal-formula-Prop (¬ₘ a)) logic)
                      ( transitive-leq-subtype x ( Id-modal-formula-Prop (¬ₘ a))
                        ( theory-add-formula (¬ₘ a) logic)
                        ( subtype-union-left
                          ( Id-modal-formula-Prop (¬ₘ a))
                          ( logic))
                        ( inv-subset-equiv-subtypes
                          (Id-modal-formula-Prop (¬ₘ a))
                          ( x)
                          ( compute-raise-subtype l2
                            ( Id-modal-formula-Prop (¬ₘ a))))))
                    ( ⊥ₘ)
                    ( bot-in-logic))))))

    canonical-model-completness :
      {l3 : Level}
      (C : model-class (lsuc l1 ⊔ lsuc l2) (l1 ⊔ l2) i (l1 ⊔ l2) l3) →
      is-in-subtype C canonical-kripke-model →
      completeness logic C
    canonical-model-completness C model-in-class a a-in-class-logic =
      backward-implication
        ( canonical-model-theorem a)
        ( a-in-class-logic canonical-kripke-model model-in-class)
```
