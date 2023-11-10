# Classical proof of completeness K

```agda
module modal-logic.classical-completeness-K where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.intersections-subtypes
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.unions-subtypes
open import foundation.universe-levels

open import order-theory.maximal-elements-posets
open import order-theory.posets
open import order-theory.preorders
open import order-theory.subposets
open import order-theory.chains-posets
open import order-theory.top-elements-posets

open import modal-logic.axioms
open import modal-logic.completeness
open import modal-logic.formulas
open import modal-logic.kripke-semantics
open import modal-logic.logic-syntax
open import modal-logic.soundness
open import modal-logic.weak-deduction
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  subtypes-leq-Preorder : Preorder (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  pr1 subtypes-leq-Preorder = subtype l2 A
  pr1 (pr2 subtypes-leq-Preorder) = leq-prop-subtype
  pr1 (pr2 (pr2 subtypes-leq-Preorder)) = refl-leq-subtype
  pr2 (pr2 (pr2 subtypes-leq-Preorder)) = transitive-leq-subtype

  subtypes-leq-Poset : Poset (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  pr1 subtypes-leq-Poset = subtypes-leq-Preorder
  pr2 subtypes-leq-Poset = antisymmetric-leq-subtype

module _
  {l1 l2 : Level} {i : Set l1} (axioms : formulas l2 i)
  (L-is-cons : is-consistent-modal-logic (weak-modal-logic axioms))
  (contains-ax-k : ax-k i ⊆ weak-modal-logic axioms)
  (contains-ax-s : ax-s i ⊆ weak-modal-logic axioms)
  (contains-ax-dn : ax-dn i ⊆ weak-modal-logic axioms)
  where

  is-L-consistent-theory-Prop : formulas (l1 ⊔ l2) i → Prop (l1 ⊔ l2)
  is-L-consistent-theory-Prop t =
    is-consistent-modal-logic-Prop (weak-modal-logic (union-subtype axioms t))

  is-L-consistent-theory : formulas (l1 ⊔ l2) i → UU (l1 ⊔ l2)
  is-L-consistent-theory = type-Prop ∘ is-L-consistent-theory-Prop

  L-consistent-theory : UU (lsuc l1 ⊔ lsuc l2)
  L-consistent-theory = Σ (formulas (l1 ⊔ l2) i) is-L-consistent-theory

  L-consistent-theory-leq-Prop :
    L-consistent-theory → L-consistent-theory → Prop (l1 ⊔ l2)
  L-consistent-theory-leq-Prop x y = leq-prop-subtype (pr1 x) (pr1 y)

  L-consistent-theory-leq : L-consistent-theory → L-consistent-theory → UU (l1 ⊔ l2)
  L-consistent-theory-leq x y = type-Prop (L-consistent-theory-leq-Prop x y)

  theories-Poset : Poset (lsuc l1 ⊔ lsuc l2) (l1 ⊔ l2)
  theories-Poset = subtypes-leq-Poset (l1 ⊔ l2) (formula i)

  L-consistent-theories-Poset : Poset (lsuc l1 ⊔ lsuc l2) (l1 ⊔ l2)
  L-consistent-theories-Poset =
    poset-Subposet theories-Poset is-L-consistent-theory-Prop

  is-L-complete-theory-Prop : L-consistent-theory → Prop (lsuc l1 ⊔ lsuc l2)
  is-L-complete-theory-Prop =
    is-maximal-element-Poset-Prop L-consistent-theories-Poset

  is-L-complete-theory : L-consistent-theory → UU (lsuc l1 ⊔ lsuc l2)
  is-L-complete-theory = type-Prop ∘ is-L-complete-theory-Prop

  complete-theory-closed :
    (x : L-consistent-theory) → is-L-complete-theory x →
    {a : formula i} → pr1 x ▷ a → is-in-subtype (pr1 x) a
  complete-theory-closed x is-comp {a} wd =
    tr
      ( λ y → is-in-subtype (pr1 y) a)
      ( is-comp
        ( theory-add-formula a (pr1 x)
        , λ bot-in-logic →
          ( pr2 x
            ( subset-weak-modal-logic-if-subset-axioms
              ( subtype-union-both
                ( axioms)
                ( theory-add-formula a (pr1 x))
                ( weak-modal-logic (union-subtype axioms (pr1 x)))
                ( transitive-leq-subtype
                  ( axioms)
                  ( union-subtype axioms (pr1 x))
                  ( weak-modal-logic (union-subtype axioms (pr1 x)))
                  ( axioms-subset-weak-modal-logic
                    ( union-subtype axioms (pr1 x)))
                  ( subtype-union-left axioms (pr1 x)))
                ( subtype-union-both
                  ( Id-formula-Prop a)
                  ( pr1 x)
                  ( weak-modal-logic (union-subtype axioms (pr1 x)))
                  ( λ { .a refl →
                    ( weak-modal-logic-monotic
                      ( subtype-union-right axioms (pr1 x))
                      ( a)
                      ( unit-trunc-Prop wd)) })
                  ( transitive-leq-subtype
                    ( pr1 x)
                    ( union-subtype axioms (pr1 x))
                    ( weak-modal-logic (union-subtype axioms (pr1 x)))
                    ( axioms-subset-weak-modal-logic
                      (union-subtype axioms (pr1 x)))
                    ( subtype-union-right axioms (pr1 x)))))
              ( ⊥)
              ( bot-in-logic))))
        ( subtype-union-right (Id-formula-Prop a) (pr1 x)))
      ( unit-trunc-Prop (inl refl))

  weak-modal-logic-subset-complete-theory :
    (x : L-consistent-theory) → is-L-complete-theory x →
    weak-modal-logic (pr1 x) ⊆ pr1 x
  weak-modal-logic-subset-complete-theory x is-comp a =
    map-universal-property-trunc-Prop
      ( pr1 x a)
      ( complete-theory-closed x is-comp)

  deduction-axioms-L-complete-theory :
    (x : L-consistent-theory) → is-L-complete-theory x →
    {a : formula i} → axioms ▷ a → is-in-subtype (pr1 x) a
  deduction-axioms-L-complete-theory x is-comp {a} wd =
    tr
      ( λ y → is-in-subtype (pr1 y) a)
      ( is-comp
        ( theory-add-formula a (pr1 x)
        , λ bot-in-logic →
          ( pr2 x
            ( subset-weak-modal-logic-if-subset-axioms
              ( subtype-union-both
                ( axioms)
                ( theory-add-formula a (pr1 x))
                ( weak-modal-logic (union-subtype axioms (pr1 x)))
                ( transitive-leq-subtype
                  ( axioms)
                  ( union-subtype axioms (pr1 x))
                  ( weak-modal-logic (union-subtype axioms (pr1 x)))
                  ( axioms-subset-weak-modal-logic
                    ( union-subtype axioms (pr1 x)))
                  ( subtype-union-left axioms (pr1 x)))
                ( subtype-union-both
                  ( Id-formula-Prop a)
                  ( pr1 x)
                  ( weak-modal-logic (union-subtype axioms (pr1 x)))
                  ( λ { .a refl →
                    ( weak-modal-logic-monotic
                      ( subtype-union-left axioms (pr1 x))
                      ( a)
                      ( unit-trunc-Prop wd)) })
                  ( transitive-leq-subtype
                    ( pr1 x)
                    ( union-subtype axioms (pr1 x))
                    ( weak-modal-logic (union-subtype axioms (pr1 x)))
                    ( axioms-subset-weak-modal-logic
                      (union-subtype axioms (pr1 x)))
                    ( subtype-union-right axioms (pr1 x)))))
              ( ⊥)
              ( bot-in-logic))))
        ( subtype-union-right (Id-formula-Prop a) (pr1 x)))
      ( subtype-union-left (Id-formula-Prop a) (pr1 x) a refl)

  logic-subset-L-complete-theory :
    (x : L-consistent-theory) → is-L-complete-theory x →
    weak-modal-logic (axioms) ⊆ pr1 x
  logic-subset-L-complete-theory x is-comp a =
    map-universal-property-trunc-Prop
      ( pr1 x a)
      ( deduction-axioms-L-complete-theory x is-comp)

  axioms-subset-L-complete-theory :
    (x : L-consistent-theory) → is-L-complete-theory x → axioms ⊆ pr1 x
  axioms-subset-L-complete-theory x is-comp =
    transitive-leq-subtype
      ( axioms)
      ( weak-modal-logic axioms)
      ( pr1 x)
      ( logic-subset-L-complete-theory x is-comp)
      ( axioms-subset-weak-modal-logic axioms)

  complete-theory-contains-all-formulas :
    LEM (l1 ⊔ l2) →
    (x : L-consistent-theory) → is-L-complete-theory x →
    (a : formula i) → type-disj-Prop ((pr1 x) a) ((pr1 x) (~ a))
  complete-theory-contains-all-formulas lem x is-comp a with lem ((pr1 x) a)
  ... | inl a-in-logic = inl-disj-Prop ((pr1 x) a) ((pr1 x) (~ a)) a-in-logic
  ... | inr a-not-in-logic =
    unit-trunc-Prop
      ( inr
        ( tr
          ( λ y → is-in-subtype (pr1 y) (~ a))
          ( is-comp
            ( theory-add-formula (~ a) (pr1 x)
            , λ bot-in-logic →
              ( a-not-in-logic
                ( weak-modal-logic-subset-complete-theory
                  ( x)
                  ( is-comp)
                  ( a)
                  ( apply-universal-property-trunc-Prop
                    ( forward-implication
                      ( deduction-lemma
                        ( pr1 x)
                        ( transitive-leq-subtype
                          ( ax-k i)
                          ( weak-modal-logic (axioms))
                          ( weak-modal-logic (pr1 x))
                          ( weak-modal-logic-monotic
                            ( axioms-subset-L-complete-theory x is-comp))
                          ( contains-ax-k))
                        (  transitive-leq-subtype
                          ( ax-s i)
                          ( weak-modal-logic (axioms))
                          ( weak-modal-logic (pr1 x))
                          ( weak-modal-logic-monotic
                            ( axioms-subset-L-complete-theory x is-comp))
                          ( contains-ax-s))
                        ( ~ a)
                        ( ⊥))
                      ( weak-modal-logic-monotic
                        { ax₁ = union-subtype axioms (theory-add-formula (~ a) (pr1 x))}
                        { ax₂ = theory-add-formula (~ a) (pr1 x)}
                        ( subtype-union-both
                          ( axioms)
                          ( theory-add-formula (~ a) (pr1 x))
                          ( theory-add-formula (~ a) (pr1 x))
                          ( transitive-leq-subtype
                            ( axioms)
                            ( pr1 x)
                            ( theory-add-formula (~ a) (pr1 x))
                            ( subtype-union-right
                              ( Id-formula-Prop (~ a))
                              ( pr1 x))
                            ( axioms-subset-L-complete-theory x is-comp))
                          ( refl-leq-subtype
                            ( theory-add-formula (~ a) (pr1 x))))
                        ( ⊥)
                        ( bot-in-logic)))
                    ( weak-modal-logic (pr1 x) a)
                    ( λ wd-bot →
                      ( unit-trunc-Prop
                        ( w-mp
                          ( w-ax
                            ( logic-subset-L-complete-theory
                              ( x)
                              ( is-comp)
                              ( ~~ a ⇒ a)
                              ( contains-ax-dn _ (a , refl))))
                          ( wd-bot))))))))
            ( subtype-union-right (Id-formula-Prop (~ a)) (pr1 x)))
          ( subtype-union-left (Id-formula-Prop (~ a)) (pr1 x) (~ a) refl)))
    -- tr
    --   ( λ y → type-disj-Prop ((pr1 y) a) ((pr1 y) (~ a)))
    --   ( is-comp
    --     ( theory-add-formula (~ a) (pr1 x)
    --     , λ bot-in-logic →
    --       ( {!   !}))
    --     ( subtype-union-right (Id-formula-Prop (~ a)) (pr1 x)))
    --   ( unit-trunc-Prop
    --     ( inr (subtype-union-left (Id-formula-Prop (~ a)) (pr1 x) (~ a) refl)))

  complete-theory-implication :
    LEM (l1 ⊔ l2) →
    (x : L-consistent-theory) → is-L-complete-theory x →
    {a b : formula i} → (is-in-subtype (pr1 x) a → is-in-subtype (pr1 x) b) →
    is-in-subtype (pr1 x) (a ⇒ b)
  complete-theory-implication lem x is-comp {a} {b} imp =
    apply-universal-property-trunc-Prop
      ( complete-theory-contains-all-formulas lem x is-comp a)
      ( (pr1 x) (a ⇒ b))
      ( λ { (inl a-in-logic) →
              ( weak-modal-logic-subset-complete-theory
                ( x)
                ( is-comp)
                ( a ⇒ b)
                ( forward-implication
                  ( deduction-lemma
                    ( pr1 x)
                    ( transitive-leq-subtype
                      ( ax-k i)
                      ( weak-modal-logic axioms)
                      ( weak-modal-logic (pr1 x))
                      ( transitive-leq-subtype
                        ( weak-modal-logic axioms)
                        ( pr1 x)
                        ( weak-modal-logic (pr1 x))
                        ( axioms-subset-weak-modal-logic (pr1 x))
                        ( logic-subset-L-complete-theory x is-comp))
                      ( contains-ax-k))
                    ( transitive-leq-subtype
                      ( ax-s i)
                      ( weak-modal-logic axioms)
                      ( weak-modal-logic (pr1 x))
                      ( transitive-leq-subtype
                        ( weak-modal-logic axioms)
                        ( pr1 x)
                        ( weak-modal-logic (pr1 x))
                        ( axioms-subset-weak-modal-logic (pr1 x))
                        ( logic-subset-L-complete-theory x is-comp))
                      ( contains-ax-s))
                    ( a)
                    ( b))
                  ( weak-modal-logic-monotic
                    { ax₁ = pr1 x} -- TODO : make explicit
                    { ax₂ = union-subtype (Id-formula-Prop a) (pr1 x)}
                    ( subtype-union-right (Id-formula-Prop a) (pr1 x))
                    ( b)
                    ( unit-trunc-Prop (w-ax (imp a-in-logic))))))
          ; (inr not-a-in-logic) →
              ( weak-modal-logic-subset-complete-theory
                ( x)
                ( is-comp)
                ( a ⇒ b)
                ( forward-implication
                  ( deduction-lemma
                    ( pr1 x)
                    ( transitive-leq-subtype
                      ( ax-k i)
                      ( weak-modal-logic axioms)
                      ( weak-modal-logic (pr1 x))
                      ( transitive-leq-subtype
                        ( weak-modal-logic axioms)
                        ( pr1 x)
                        ( weak-modal-logic (pr1 x))
                        ( axioms-subset-weak-modal-logic (pr1 x))
                        ( logic-subset-L-complete-theory x is-comp))
                      ( contains-ax-k))
                    ( transitive-leq-subtype
                      ( ax-s i)
                      ( weak-modal-logic axioms)
                      ( weak-modal-logic (pr1 x))
                      ( transitive-leq-subtype
                        ( weak-modal-logic axioms)
                        ( pr1 x)
                        ( weak-modal-logic (pr1 x))
                        ( axioms-subset-weak-modal-logic (pr1 x))
                        ( logic-subset-L-complete-theory x is-comp))
                      ( contains-ax-s))
                    ( a)
                    ( b))
                  ( logic-ex-falso
                    ( theory-add-formula a (pr1 x))
                    ( transitive-leq-subtype
                      ( ax-k i)
                      ( weak-modal-logic (pr1 x))
                      ( weak-modal-logic (theory-add-formula a (pr1 x)))
                      ( weak-modal-logic-monotic
                        ( subtype-union-right (Id-formula-Prop a) (pr1 x)))
                      ( transitive-leq-subtype
                        ( ax-k i)
                        ( weak-modal-logic axioms)
                        ( weak-modal-logic (pr1 x))
                        ( transitive-leq-subtype
                          ( weak-modal-logic axioms)
                          ( pr1 x)
                          ( weak-modal-logic (pr1 x))
                          ( axioms-subset-weak-modal-logic (pr1 x))
                          ( logic-subset-L-complete-theory x is-comp))
                        ( contains-ax-k)))
                    ( transitive-leq-subtype
                      ( ax-s i)
                      ( weak-modal-logic (pr1 x))
                      ( weak-modal-logic (theory-add-formula a (pr1 x)))
                      ( weak-modal-logic-monotic
                        ( subtype-union-right (Id-formula-Prop a) (pr1 x)))
                      ( transitive-leq-subtype
                        ( ax-s i)
                        ( weak-modal-logic axioms)
                        ( weak-modal-logic (pr1 x))
                        ( transitive-leq-subtype
                          ( weak-modal-logic axioms)
                          ( pr1 x)
                          ( weak-modal-logic (pr1 x))
                          ( axioms-subset-weak-modal-logic (pr1 x))
                          ( logic-subset-L-complete-theory x is-comp))
                        ( contains-ax-s)))
                    ( transitive-leq-subtype
                      ( ax-dn i)
                      ( weak-modal-logic (pr1 x))
                      ( weak-modal-logic (theory-add-formula a (pr1 x)))
                      ( weak-modal-logic-monotic
                        ( subtype-union-right (Id-formula-Prop a) (pr1 x)))
                      ( transitive-leq-subtype
                        ( ax-dn i)
                        ( weak-modal-logic axioms)
                        ( weak-modal-logic (pr1 x))
                        ( transitive-leq-subtype
                          ( weak-modal-logic axioms)
                          ( pr1 x)
                          ( weak-modal-logic (pr1 x))
                          ( axioms-subset-weak-modal-logic (pr1 x))
                          ( logic-subset-L-complete-theory x is-comp))
                        ( contains-ax-dn)))
                    ( a)
                    ( b)
                    ( weak-modal-logic-monotic
                      { ax₁ = Id-formula-Prop a}
                      { ax₂ = union-subtype (Id-formula-Prop a) (pr1 x)}
                      ( subtype-union-left (Id-formula-Prop a) (pr1 x))
                      ( a)
                      ( unit-trunc-Prop (w-ax refl)))
                    ( weak-modal-logic-monotic
                      { ax₁ = pr1 x}
                      { ax₂ = union-subtype (Id-formula-Prop a) (pr1 x)}
                      ( subtype-union-right (Id-formula-Prop a) (pr1 x))
                      ( ~ a)
                      ( unit-trunc-Prop (w-ax not-a-in-logic)))))) })

  canonical-worlds : subtype (lsuc l1 ⊔ lsuc l2) (formulas (l1 ⊔ l2) i)
  canonical-worlds x =
    Σ-Prop
      ( is-L-consistent-theory-Prop x)
      ( λ is-cons → is-L-complete-theory-Prop (x , is-cons))

  canonical-kripke-model-world-type : UU (lsuc l1 ⊔ lsuc l2)
  canonical-kripke-model-world-type =
    Σ (formulas (l1 ⊔ l2) i) (is-in-subtype canonical-worlds)

  postulate
    lindenbaum :
      (x : L-consistent-theory) →
      ∃ ( L-consistent-theory)
        ( λ y → L-consistent-theory-leq x y × is-L-complete-theory y)

  is-L-consistent-axioms : is-L-consistent-theory (raise-subtype l1 axioms)
  is-L-consistent-axioms =
    map-universal-property-trunc-Prop
      ( empty-Prop)
      ( tr
        ( λ x → x ▷ ⊥ → empty)
        ( helper)
        ( λ x →
          ( L-is-cons
            ( unit-trunc-Prop
              ( deduction-equiv-axioms
                ( inv-equiv-subtypes
                  ( axioms)
                  ( raise-subtype l1 axioms)
                  ( compute-raise-subtype l1 axioms))
                ( x))))))
    where
    -- TODO: move to unions-subtypes as lemma
    helper :
      raise-subtype l1 axioms ＝ union-subtype axioms (raise-subtype l1 axioms)
    helper =
      antisymmetric-leq-subtype
        ( raise-subtype l1 axioms)
        ( union-subtype axioms (raise-subtype l1 axioms))
        ( subtype-union-right axioms (raise-subtype l1 axioms))
        ( subtype-union-both
          ( axioms)
          ( raise-subtype l1 axioms)
          ( raise-subtype l1 axioms)
          ( λ _ → map-raise)
          ( λ _ → id))

  is-inhabited-canonical-kripke-model-world :
    is-inhabited canonical-kripke-model-world-type
  is-inhabited-canonical-kripke-model-world =
    apply-universal-property-trunc-Prop
      ( lindenbaum (raise-subtype l1 axioms , is-L-consistent-axioms))
      ( is-inhabited-Prop canonical-kripke-model-world-type)
      ( λ x → unit-trunc-Prop ((pr1 (pr1 x)) , ((pr2 (pr1 x)) , (pr2 (pr2 x)))))

  canonical-kripke-model :
    kripke-model (canonical-kripke-model-world-type) (l1 ⊔ l2) i (l1 ⊔ l2)
  pr1 (pr1 canonical-kripke-model) =
    is-inhabited-canonical-kripke-model-world
  pr2 (pr1 canonical-kripke-model) x y =
    Π-Prop
      ( formula i)
      ( λ a → function-Prop (is-in-subtype (pr1 x) (□ a)) ((pr1 y) a))
  pr2 canonical-kripke-model n x = pr1 x (var n)

  module _
    (lem : LEM (l1 ⊔ l2))
    where

    canonical-model-theorem :
      (a : formula i)
      (x : canonical-kripke-model-world-type) →
      pr1 x a ⇔ ((canonical-kripke-model , x) ⊨ a)
    pr1 (canonical-model-theorem (var n) x) in-logic =
      map-raise in-logic
    pr1 (canonical-model-theorem ⊥ x) in-logic =
      map-raise
        ( pr1
          ( pr2 x)
          ( unit-trunc-Prop
            ( w-ax (subtype-union-right axioms (pr1 x) ⊥ in-logic))))
    pr1 (canonical-model-theorem (a ⇒ b) x) in-logic fa =
      pr1
        ( canonical-model-theorem b x)
        ( weak-modal-logic-subset-complete-theory
          ( pr1 x , pr1 (pr2 x))
          ( pr2 (pr2 x))
          ( b)
          ( unit-trunc-Prop
            ( w-mp
              ( w-ax in-logic)
              ( w-ax (backward-implication (canonical-model-theorem a x) fa)))))
    pr1 (canonical-model-theorem (□ a) x) in-logic y xRy =
      forward-implication (canonical-model-theorem a y) (xRy a in-logic)
    pr2 (canonical-model-theorem (var n) x) f =
      map-inv-raise f
    pr2 (canonical-model-theorem ⊥ x) (map-raise ())
    pr2 (canonical-model-theorem (a ⇒ b) x) f =
      complete-theory-implication
        ( lem)
        ( pr1 x , pr1 (pr2 x))
        ( pr2 (pr2 x))
        ( λ a-in-logic →
          ( backward-implication
            ( canonical-model-theorem b x)
            ( f
              ( forward-implication (canonical-model-theorem a x) a-in-logic))))
    pr2 (canonical-model-theorem (□ a) x) f =
      {!   !}
```
