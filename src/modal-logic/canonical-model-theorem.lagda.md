# Canonical model theorem

```agda
module modal-logic.canonical-model-theorem where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
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
open import foundation.propositional-resizing
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.unions-subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.equivalences

open import lists.lists
open import lists.reversing-lists

open import modal-logic.axioms
open import modal-logic.completeness
open import modal-logic.formulas
open import modal-logic.kripke-semantics
open import modal-logic.logic-syntax
open import modal-logic.modal-logic-K
open import modal-logic.soundness
open import modal-logic.weak-deduction

open import order-theory.chains-posets
open import order-theory.maximal-elements-posets
open import order-theory.posets
open import order-theory.preorders
open import order-theory.subposets
open import order-theory.subtypes-leq-posets
open import order-theory.top-elements-posets
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 l2 : Level} {i : Set l1} (axioms : formulas l2 i)
  (zorn : Zorn (lsuc l1 ⊔ lsuc l2) (l1 ⊔ l2) l2)
  (prop-resize : propositional-resizing (l1 ⊔ l2) (lsuc (l1 ⊔ l2)))
  (L-is-cons : is-consistent-modal-logic (modal-logic axioms))
  (contains-K : modal-logic-K i ⊆ modal-logic axioms)
  where

  logic : formulas (l1 ⊔ l2) i
  logic = modal-logic axioms

  contains-ax-k : ax-k i ⊆ logic
  contains-ax-k =
    transitive-leq-subtype
      ( ax-k i)
      ( modal-logic-K i)
      ( logic)
      ( contains-K)
      ( K-contains-ax-k i)

  contains-ax-s : ax-s i ⊆ logic
  contains-ax-s =
    transitive-leq-subtype
      ( ax-s i)
      ( modal-logic-K i)
      ( logic)
      ( contains-K)
      ( K-contains-ax-s i)

  contains-ax-n : ax-n i ⊆ logic
  contains-ax-n =
    transitive-leq-subtype
      ( ax-n i)
      ( modal-logic-K i)
      ( logic)
      ( contains-K)
      ( K-contains-ax-n i)

  contains-ax-dn : ax-dn i ⊆ logic
  contains-ax-dn =
    transitive-leq-subtype
      ( ax-dn i)
      ( modal-logic-K i)
      ( logic)
      ( contains-K)
      ( K-contains-ax-dn i)

  is-L-consistent-theory-Prop : formulas (l1 ⊔ l2) i → Prop (l1 ⊔ l2)
  is-L-consistent-theory-Prop t =
    is-consistent-modal-logic-Prop (weak-modal-logic (union-subtype logic t))

  is-L-consistent-theory : formulas (l1 ⊔ l2) i → UU (l1 ⊔ l2)
  is-L-consistent-theory = type-Prop ∘ is-L-consistent-theory-Prop

  L-consistent-theory : UU (lsuc l1 ⊔ lsuc l2)
  L-consistent-theory = Σ (formulas (l1 ⊔ l2) i) is-L-consistent-theory

  L-consistent-theory-leq-Prop :
    L-consistent-theory → L-consistent-theory → Prop (l1 ⊔ l2)
  L-consistent-theory-leq-Prop x y = leq-prop-subtype (pr1 x) (pr1 y)

  L-consistent-theory-leq :
    L-consistent-theory → L-consistent-theory → UU (l1 ⊔ l2)
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

  weak-modal-logic-subset-complete-theory :
    (x : L-consistent-theory) → is-L-complete-theory x →
    weak-modal-logic (pr1 x) ⊆ pr1 x
  weak-modal-logic-subset-complete-theory x is-comp a in-logic =
    tr
      ( λ y → is-in-subtype (pr1 y) a)
      ( is-comp
        ( pair
          ( theory-add-formula a (pr1 x))
          ( λ bot-in-logic →
            ( pr2 x
              ( subset-weak-modal-logic-if-subset-axioms
                ( transitive-leq-subtype
                  ( union-subtype logic (theory-add-formula a (pr1 x)))
                  ( theory-add-formula a (union-subtype logic (pr1 x)))
                  ( weak-modal-logic (union-subtype logic (pr1 x)))
                  ( subtype-union-both
                    ( Id-formula-Prop a)
                    ( union-subtype logic (pr1 x))
                    ( weak-modal-logic (union-subtype logic (pr1 x)))
                    ( λ { .a refl →
                      ( weak-modal-logic-monotic
                        ( subtype-union-right logic (pr1 x))
                        ( a)
                        ( in-logic))})
                    ( axioms-subset-weak-modal-logic
                      ( union-subtype logic (pr1 x))))
                  ( union-swap-1-2 logic (Id-formula-Prop a) (pr1 x)))
                ( ⊥)
                ( bot-in-logic)))))
        ( subtype-union-right (Id-formula-Prop a) (pr1 x)))
      ( unit-trunc-Prop (inl refl))

  logic-subset-L-complete-theory :
    (x : L-consistent-theory) → is-L-complete-theory x → logic ⊆ pr1 x
  logic-subset-L-complete-theory x is-comp a in-logic =
    tr
      ( λ y → is-in-subtype (pr1 y) a)
      ( is-comp
        ( pair
          ( theory-add-formula a (pr1 x))
          ( λ bot-in-logic →
            ( pr2 x
              ( weak-modal-logic-monotic
                ( transitive-leq-subtype
                  ( union-subtype logic (theory-add-formula a (pr1 x)))
                  ( union-subtype
                    ( union-subtype logic (Id-formula-Prop a)) (pr1 x))
                  ( union-subtype logic (pr1 x))
                  ( subset-union-subset-left
                    ( union-subtype logic (Id-formula-Prop a))
                    ( logic)
                    ( pr1 x)
                    ( subtype-union-both
                      ( logic)
                      ( Id-formula-Prop a)
                      ( logic)
                      ( refl-leq-subtype logic)
                      ( λ { .a refl → in-logic})))
                  ( forward-subset-union-assoc
                    ( logic)
                    ( Id-formula-Prop a)
                    ( pr1 x)))
                ( ⊥)
                ( bot-in-logic)))))
        ( subtype-union-right (Id-formula-Prop a) (pr1 x)))
      ( subtype-union-left (Id-formula-Prop a) (pr1 x) a refl)

  complete-theory-contains-all-formulas :
    LEM (l1 ⊔ l2) →
    (x : L-consistent-theory) → is-L-complete-theory x →
    (a : formula i) → type-disjunction-Prop (pr1 x a) (pr1 x (~ a))
  complete-theory-contains-all-formulas lem x is-comp a with lem ((pr1 x) a)
  ... | inl a-in-logic = inl-disjunction-Prop ((pr1 x) a) ((pr1 x) (~ a)) a-in-logic
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
                          ( logic)
                          ( weak-modal-logic (pr1 x))
                          ( transitive-leq-subtype
                            ( logic)
                            ( pr1 x)
                            ( weak-modal-logic (pr1 x))
                            ( axioms-subset-weak-modal-logic (pr1 x))
                            ( logic-subset-L-complete-theory x is-comp))
                          ( contains-ax-k))
                        ( transitive-leq-subtype
                          ( ax-s i)
                          ( logic)
                          ( weak-modal-logic (pr1 x))
                          ( transitive-leq-subtype
                            ( logic)
                            ( pr1 x)
                            ( weak-modal-logic (pr1 x))
                            ( axioms-subset-weak-modal-logic (pr1 x))
                            ( logic-subset-L-complete-theory x is-comp))
                          ( contains-ax-s))
                        ( ~ a)
                        ( ⊥))
                      ( weak-modal-logic-monotic
                        { ax₁ =
                          ( union-subtype logic
                            ( theory-add-formula (~ a) (pr1 x)))}
                        { ax₂ = theory-add-formula (~ a) (pr1 x)}
                        ( subtype-union-both
                          ( logic)
                          ( theory-add-formula (~ a) (pr1 x))
                          ( theory-add-formula (~ a) (pr1 x))
                          ( transitive-leq-subtype
                            ( logic)
                            ( pr1 x)
                            ( theory-add-formula (~ a) (pr1 x))
                            ( subtype-union-right
                              ( Id-formula-Prop (~ a))
                              ( pr1 x))
                            ( logic-subset-L-complete-theory x is-comp))
                          ( refl-leq-subtype
                            (theory-add-formula (~ a) (pr1 x))))
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
                              ( ~~ a →ₘ a)
                              ( contains-ax-dn _ (a , refl))))
                          ( wd-bot))))))))
            ( subtype-union-right (Id-formula-Prop (~ a)) (pr1 x)))
          ( subtype-union-left (Id-formula-Prop (~ a)) (pr1 x) (~ a) refl)))

  complete-theory-implication :
    LEM (l1 ⊔ l2) →
    (x : L-consistent-theory) → is-L-complete-theory x →
    {a b : formula i} → (is-in-subtype (pr1 x) a → is-in-subtype (pr1 x) b) →
    is-in-subtype (pr1 x) (a →ₘ b)
  complete-theory-implication lem x is-comp {a} {b} imp =
    apply-universal-property-trunc-Prop
      ( complete-theory-contains-all-formulas lem x is-comp a)
      ( pr1 x (a →ₘ b))
      ( λ { (inl a-in-logic) →
              ( weak-modal-logic-subset-complete-theory
                ( x)
                ( is-comp)
                ( a →ₘ b)
                ( forward-implication
                  ( deduction-lemma
                    ( pr1 x)
                    ( transitive-leq-subtype
                      ( ax-k i)
                      ( logic)
                      ( weak-modal-logic (pr1 x))
                      ( transitive-leq-subtype
                        ( logic)
                        ( pr1 x)
                        ( weak-modal-logic (pr1 x))
                        ( axioms-subset-weak-modal-logic (pr1 x))
                        ( logic-subset-L-complete-theory x is-comp))
                      ( contains-ax-k))
                    ( transitive-leq-subtype
                      ( ax-s i)
                      ( logic)
                      ( weak-modal-logic (pr1 x))
                      ( transitive-leq-subtype
                        ( logic)
                        ( pr1 x)
                        ( weak-modal-logic (pr1 x))
                        ( axioms-subset-weak-modal-logic (pr1 x))
                        ( logic-subset-L-complete-theory x is-comp))
                      ( contains-ax-s))
                    ( a)
                    ( b))
                  ( weak-modal-logic-monotic
                    { ax₁ = pr1 x} -- TODO: make explicit
                    { ax₂ = union-subtype (Id-formula-Prop a) (pr1 x)}
                    ( subtype-union-right (Id-formula-Prop a) (pr1 x))
                    ( b)
                    ( unit-trunc-Prop (w-ax (imp a-in-logic))))))
          ; (inr not-a-in-logic) →
              ( weak-modal-logic-subset-complete-theory
                ( x)
                ( is-comp)
                ( a →ₘ b)
                ( forward-implication
                  ( deduction-lemma
                    ( pr1 x)
                    ( transitive-leq-subtype
                      ( ax-k i)
                      ( logic)
                      ( weak-modal-logic (pr1 x))
                      ( transitive-leq-subtype
                        ( logic)
                        ( pr1 x)
                        ( weak-modal-logic (pr1 x))
                        ( axioms-subset-weak-modal-logic (pr1 x))
                        ( logic-subset-L-complete-theory x is-comp))
                      ( contains-ax-k))
                    ( transitive-leq-subtype
                      ( ax-s i)
                      ( logic)
                      ( weak-modal-logic (pr1 x))
                      ( transitive-leq-subtype
                        ( logic)
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
                        ( logic)
                        ( weak-modal-logic (pr1 x))
                        ( transitive-leq-subtype
                          ( logic)
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
                        ( logic)
                        ( weak-modal-logic (pr1 x))
                        ( transitive-leq-subtype
                          ( logic)
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
                        ( logic)
                        ( weak-modal-logic (pr1 x))
                        ( transitive-leq-subtype
                          ( logic)
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
                      ( unit-trunc-Prop (w-ax not-a-in-logic))))))})

  canonical-worlds : subtype (lsuc l1 ⊔ lsuc l2) (formulas (l1 ⊔ l2) i)
  canonical-worlds x =
    Σ-Prop
      ( is-L-consistent-theory-Prop x)
      ( λ is-cons → is-L-complete-theory-Prop (x , is-cons))

  canonical-kripke-model-world-type : UU (lsuc l1 ⊔ lsuc l2)
  canonical-kripke-model-world-type =
    Σ (formulas (l1 ⊔ l2) i) (is-in-subtype canonical-worlds)

  lindenbaum :
    (x : L-consistent-theory) →
    ∃ ( L-consistent-theory)
      ( λ y → L-consistent-theory-leq x y × is-L-complete-theory y)
  lindenbaum x =
    apply-universal-property-trunc-Prop
      ( zorn
        ( L-consistent-big-theories-Poset)
        ( unit-trunc-Prop ( x , refl-leq-subtype (pr1 x)))
        ( λ C is-inhabited-C →
          ( intro-∃
            ( pair
              ( pair
                ( resized-chain-union C)
                ( is-L-consistent-union C is-inhabited-C))
              ( λ a a-in-x →
                ( map-equiv
                  ( inv-equiv (is-equiv-resize prop-resize (chain-union C a)))
                  ( apply-universal-property-trunc-Prop
                    ( is-inhabited-C)
                    ( exists-Prop
                      ( type-subtype (pr1 C))
                      ( λ s → pr1 (pr1 (pr1 s)) a))
                    ( λ y → intro-∃ y (pr2 (pr1 y) a a-in-x))))))
            ( λ y a a-in-y →
              ( map-equiv
                ( inv-equiv (is-equiv-resize prop-resize (chain-union C a)))
                ( intro-∃ y a-in-y))))))
      ( ∃-Prop
        ( L-consistent-theory)
        ( λ y → L-consistent-theory-leq x y × is-L-complete-theory y))
      ( λ ((m , x-leq-m) , is-max) →
        ( intro-∃ m
          ( x-leq-m , λ y m-leq-y →
            ( ap pr1
              ( is-max
                ( pair y
                  ( transitive-leq-Poset
                    ( L-consistent-theories-Poset)
                    ( x)
                    ( m)
                    ( y)
                    ( m-leq-y)
                    ( x-leq-m)))
                ( m-leq-y))))))
    where
    L-consistent-big-theories-Poset : Poset (lsuc l1 ⊔ lsuc l2) (l1 ⊔ l2)
    L-consistent-big-theories-Poset =
      poset-Subposet
        ( L-consistent-theories-Poset)
        ( L-consistent-theory-leq-Prop x)

    chain-union :
      chain-Poset l2 L-consistent-big-theories-Poset →
      formulas (lsuc l1 ⊔ lsuc l2) i
    chain-union C a =
      exists-Prop
        ( type-subtype
          ( sub-preorder-chain-Poset
            ( L-consistent-big-theories-Poset)
            ( C)))
        ( λ s → pr1 (pr1 (pr1 s)) a)

    resized-chain-union :
      chain-Poset l2 L-consistent-big-theories-Poset → type-Poset theories-Poset
    resized-chain-union C = resize prop-resize ∘ chain-union C

    in-chain-weak-deduction-list-chain-union :
      (C : chain-Poset l2 L-consistent-big-theories-Poset)
      (e : type-chain-Poset L-consistent-big-theories-Poset C)
      {a : formula i}
      {l : list (formula i)} →
      in-list l ⊆ union-subtype logic (chain-union C) →
      in-list l ▷ a →
      ∃ ( type-chain-Poset L-consistent-big-theories-Poset C)
        ( λ y →
          ( is-in-subtype
            ( weak-modal-logic (union-subtype logic (pr1 (pr1 (pr1 y)))))
            ( a)))
    in-chain-weak-deduction-list-chain-union C e {a} {nil} sub wd =
      intro-∃ e (ex-falso (nil-no-deduction wd))
    in-chain-weak-deduction-list-chain-union
      C e {a} {cons y l} sub (w-ax is-ax) =
      apply-universal-property-trunc-Prop
        ( sub a is-ax)
        ( ∃-Prop ( type-chain-Poset L-consistent-big-theories-Poset C)
          ( λ y →
            ( is-in-subtype
              ( weak-modal-logic (union-subtype logic (pr1 (pr1 (pr1 y)))))
              ( a))))
        ( λ
          { (inl in-logic) →
            ( intro-∃ e
              ( weak-modal-logic-ax
                ( subtype-union-left logic (pr1 (pr1 (pr1 e))) a in-logic)))
          ; (inr in-union) →
            ( apply-universal-property-trunc-Prop
              ( in-union)
              ( ∃-Prop ( type-chain-Poset L-consistent-big-theories-Poset C)
                ( λ y →
                  ( is-in-subtype
                    ( weak-modal-logic
                      ( union-subtype logic (pr1 (pr1 (pr1 y)))))
                    ( a))))
              ( λ (y , a-in-y) →
                ( intro-∃ y
                  ( weak-modal-logic-ax
                    (subtype-union-right
                      ( logic)
                      ( pr1 (pr1 (pr1 y)))
                      ( a)
                      ( a-in-y))))))})
    in-chain-weak-deduction-list-chain-union
      C e {a} {l@(cons _ _)} sub (w-mp {b} wdba wdb) =
      apply-twice-universal-property-trunc-Prop
        ( in-chain-weak-deduction-list-chain-union C e {l = l} sub wdba)
        ( in-chain-weak-deduction-list-chain-union C e {l = l} sub wdb)
        ( ∃-Prop
          ( type-chain-Poset L-consistent-big-theories-Poset C)
          ( λ y →
            ( is-in-subtype
              ( weak-modal-logic (union-subtype logic (pr1 (pr1 (pr1 y)))))
              ( a))))
        ( λ (y , ba-in-y) (z , b-in-z) →
          ( apply-universal-property-trunc-Prop
            ( pr2 C y z)
            ( ∃-Prop
              ( type-chain-Poset L-consistent-big-theories-Poset C)
              ( λ y →
                ( is-in-subtype
                  ( weak-modal-logic (union-subtype logic (pr1 (pr1 (pr1 y)))))
                  ( a))))
            ( λ
              { (inl y-leq-z) →
                ( intro-∃ z
                  ( weak-modal-logic-mp
                    ( weak-modal-logic-monotic
                      {ax₁ = union-subtype logic (pr1 (pr1 (pr1 y)))}
                      {ax₂ = union-subtype logic (pr1 (pr1 (pr1 z)))}
                      ( subset-union-subset-right
                        ( logic)
                        ( pr1 (pr1 (pr1 y)))
                        ( pr1 (pr1 (pr1 z)))
                        ( y-leq-z))
                      ( b →ₘ a)
                      ( ba-in-y))
                    ( b-in-z)))
              ; (inr z-leq-y) →
                ( intro-∃ y
                  ( weak-modal-logic-mp
                    (ba-in-y)
                    ( weak-modal-logic-monotic
                      {ax₁ = union-subtype logic (pr1 (pr1 (pr1 z)))}
                      {ax₂ = union-subtype logic (pr1 (pr1 (pr1 y)))}
                      ( subset-union-subset-right
                        ( logic)
                        ( pr1 (pr1 (pr1 z)))
                        ( pr1 (pr1 (pr1 y)))
                        ( z-leq-y))
                      ( b)
                      ( b-in-z))))})))

    in-chain-in-chain-union :
      (C : chain-Poset l2 L-consistent-big-theories-Poset) →
      is-inhabited (type-chain-Poset L-consistent-big-theories-Poset C) →
      {a : formula i} →
      is-in-subtype
        ( weak-modal-logic (union-subtype logic (chain-union C))) a →
      ∃ ( type-subtype
          ( sub-preorder-chain-Poset L-consistent-big-theories-Poset C))
        ( λ x →
          ( is-in-subtype
            ( weak-modal-logic (union-subtype logic (pr1 (pr1 (pr1 x)))))
            ( a)))
    in-chain-in-chain-union C is-inhabited-C {a} in-union =
      apply-twice-universal-property-trunc-Prop
        ( in-union)
        ( is-inhabited-C)
        ( ∃-Prop
          ( type-subtype
            ( sub-preorder-chain-Poset L-consistent-big-theories-Poset C))
            ( λ x →
              ( is-in-subtype
                ( weak-modal-logic (union-subtype logic (pr1 (pr1 (pr1 x)))))
                ( a))))
        ( λ wd c →
          ( let (l , sub , wdl) = list-assumptions-weak-deduction wd
            in in-chain-weak-deduction-list-chain-union C c sub wdl))

    is-L-consistent-union :
      (C : chain-Poset l2 L-consistent-big-theories-Poset) →
      is-inhabited (type-chain-Poset L-consistent-big-theories-Poset C) →
      is-L-consistent-theory (resized-chain-union C)
    is-L-consistent-union C C-is-inhabited bot-in-union =
      apply-universal-property-trunc-Prop
        ( in-chain-in-chain-union C C-is-inhabited
          ( weak-modal-logic-monotic
            {ax₁ = union-subtype logic (resized-chain-union C)}
            {ax₂ = union-subtype logic (chain-union C)}
            ( subset-union-subset-right
              ( logic)
              ( resized-chain-union C)
              ( chain-union C)
              ( λ b →
                ( map-equiv (is-equiv-resize prop-resize (chain-union C b)))))
            ( ⊥)
            ( bot-in-union)))
        ( empty-Prop)
        ( λ (y , bot-in-y) → pr2 (pr1 (pr1 y)) bot-in-y)

  is-L-consistent-logic : is-L-consistent-theory logic
  is-L-consistent-logic bot-in-logic =
    L-is-cons
      ( transitive-leq-subtype
        ( weak-modal-logic (union-subtype logic logic))
        ( modal-logic (union-subtype logic logic))
        ( logic)
        ( transitive-leq-subtype
          ( modal-logic (union-subtype logic logic))
          ( modal-logic logic)
          ( logic)
          ( subset-double-modal-logic axioms)
          ( modal-logic-monotic
            ( subtype-union-both
              ( logic)
              ( logic)
              ( logic)
              ( refl-leq-subtype logic)
              ( refl-leq-subtype logic))))
        ( weak-modal-logic-subset-modal-logic (union-subtype logic logic))
        ( ⊥)
        ( bot-in-logic))

  is-inhabited-canonical-kripke-model-world :
    is-inhabited canonical-kripke-model-world-type
  is-inhabited-canonical-kripke-model-world =
    apply-universal-property-trunc-Prop
      ( lindenbaum (logic , is-L-consistent-logic))
      ( is-inhabited-Prop canonical-kripke-model-world-type)
      ( λ x → unit-trunc-Prop ((pr1 (pr1 x)) , ((pr2 (pr1 x)) , (pr2 (pr2 x)))))

  canonical-kripke-model :
    kripke-model (canonical-kripke-model-world-type) (l1 ⊔ l2) i (l1 ⊔ l2)
  pr1 (pr1 canonical-kripke-model) =
    is-inhabited-canonical-kripke-model-world
  pr2 (pr1 canonical-kripke-model) x y =
    Π-Prop
      ( formula i)
      ( λ a → hom-Prop (pr1 x (□ a)) (pr1 y a))
  pr2 canonical-kripke-model n x = pr1 x (var n)

  complete-theory-box :
    LEM (l1 ⊔ l2) →
    (x : L-consistent-theory)
    (is-comp : is-L-complete-theory x)
    (a : formula i) →
    ( (y : formulas (l1 ⊔ l2) i) →
      (is-canonical : is-in-subtype canonical-worlds y) →
      model-relation i canonical-kripke-model
        ( pr1 x , pr2 x , is-comp)
        ( y , is-canonical) →
      is-in-subtype y a) →
    is-in-subtype (pr1 x) (□ a)
  complete-theory-box lem x is-comp a h =
    apply-universal-property-trunc-Prop
      ( complete-theory-contains-all-formulas lem x is-comp (□ a))
      ( pr1 x (□ a))
      ( λ { (inl box-in-logic) → box-in-logic
          ; (inr not-box-in-logic) →
            ( ex-falso
              ( apply-universal-property-trunc-Prop
                ( lindenbaum (w not-box-in-logic))
                ( empty-Prop)
                ( λ (y , w-leq-y , y-is-comp) →
                  ( pr2 y
                    ( weak-modal-logic-monotic
                      { ax₁ = pr1 y}
                      { ax₂ = union-subtype logic (pr1 y)}
                      ( subtype-union-right logic (pr1 y))
                      ( ⊥)
                      ( weak-modal-logic-mp
                        ( axioms-subset-weak-modal-logic
                          ( pr1 y)
                          ( ~ a)
                          ( w-leq-y
                            ( ~ a)
                            ( subtype-union-left
                              ( Id-formula-Prop (~ a))
                              ( λ b → pr1 x (□ b))
                              ( ~ a)
                              ( refl))))
                        ( weak-modal-logic-ax
                          ( h (pr1 y) (pr2 y , y-is-comp)
                            ( λ b box-in-logic →
                              ( w-leq-y b
                                ( subtype-union-right
                                  ( Id-formula-Prop (~ a))
                                  ( λ b → pr1 x (□ b))
                                  ( b)
                                  ( box-in-logic))))))))))))})
    where

    list-to-implications :
      formula i →
      (l : list (formula i)) →
      formula i
    list-to-implications f nil = f
    list-to-implications f (cons g l) = list-to-implications (g →ₘ f) l

    list-to-implications-rev :
      formula i →
      (l : list (formula i)) →
      formula i
    list-to-implications-rev f nil = f
    list-to-implications-rev f (cons g l) = g →ₘ list-to-implications-rev f l

    list-to-implication-rev-snoc :
      (f g : formula i) (l : list (formula i)) →
      list-to-implications f (snoc l g) ＝ g →ₘ list-to-implications f l
    list-to-implication-rev-snoc f g nil = refl
    list-to-implication-rev-snoc f g (cons h l) =
      list-to-implication-rev-snoc (h →ₘ f) g l

    reverse-list-to-implications :
      (f : formula i) (l : list (formula i)) →
      list-to-implications f (reverse-list l) ＝ list-to-implications-rev f l
    reverse-list-to-implications f nil = refl
    reverse-list-to-implications f (cons g l) =
      ( list-to-implication-rev-snoc f g (reverse-list l)) ∙
      ( ap (λ x → g →ₘ x) (reverse-list-to-implications f l))

    move-right :
      {l' : Level} (axioms : formulas l' i)
      (f : formula i) (l : list (formula i)) →
      ax-k i ⊆ weak-modal-logic axioms →
      ax-s i ⊆ weak-modal-logic axioms →
      is-in-subtype (weak-modal-logic (union-subtype axioms (in-list l))) f →
      is-in-subtype (weak-modal-logic axioms) (list-to-implications f l)
    move-right axioms f nil _ _ =
      weak-modal-logic-monotic
        ( subtype-union-both
          ( axioms)
          ( in-list nil)
          ( axioms)
          ( refl-leq-subtype axioms)
          ( λ _ → ex-falso ∘ empty-in-list-nil))
        ( f)
    move-right axioms f (cons c l) contains-ax-k contains-ax-s wd =
      move-right axioms (c →ₘ f) l contains-ax-k contains-ax-s
        ( forward-implication
          ( deduction-lemma
            ( union-subtype axioms (in-list l))
            ( transitive-leq-subtype
              ( ax-k i)
              ( weak-modal-logic axioms)
              ( weak-modal-logic (union-subtype axioms (in-list l)))
              ( weak-modal-logic-monotic
                ( subtype-union-left axioms (in-list l)))
              ( contains-ax-k))
            ( transitive-leq-subtype
              ( ax-s i)
              ( weak-modal-logic axioms)
              ( weak-modal-logic (union-subtype axioms (in-list l)))
              ( weak-modal-logic-monotic
                ( subtype-union-left axioms (in-list l)))
              ( contains-ax-s))
            ( c)
            ( f))
          ( weak-modal-logic-monotic
            ( transitive-leq-subtype
              ( union-subtype axioms (in-list (cons c l)))
              ( union-subtype axioms (theory-add-formula c (in-list l)))
              ( theory-add-formula c (union-subtype axioms (in-list l)))
              ( union-swap-1-2 axioms (Id-formula-Prop c) (in-list l))
              ( subset-union-subset-right
                ( axioms)
                ( in-list (cons c l))
                ( theory-add-formula c (in-list l))
                ( backward-subset-head-add c l)))
            ( f)
            ( wd)))

    aux'''' :
      (l : list (formula i)) →
      in-list l ⊆ (λ b → pr1 x (□ b)) →
      is-in-subtype
        ( weak-modal-logic (union-subtype logic (pr1 x)))
        ( □ (list-to-implications-rev a l)) →
      is-in-subtype (weak-modal-logic (union-subtype logic (pr1 x))) (□ a)
    aux'''' nil sub in-logic = in-logic
    aux'''' (cons c l) sub in-logic =
      aux'''' l
        ( transitive-leq-subtype
          ( in-list l)
          ( in-list (cons c l))
          ( λ b → pr1 x (□ b))
          ( sub)
          ( subset-in-tail c l))
        ( weak-modal-logic-mp
          { a = □ c}
          { b = □ (list-to-implications-rev a l)}
          ( weak-modal-logic-mp
            { a = □ (c →ₘ list-to-implications-rev a l)}
            { b = □ c →ₘ □ (list-to-implications-rev a l)}
            ( weak-modal-logic-monotic
              { ax₁ = logic}
              { ax₂ = union-subtype logic (pr1 x)}
              ( subtype-union-left logic (pr1 x))
              ( □ (c →ₘ list-to-implications-rev a l) →ₘ
                □ c →ₘ □ list-to-implications-rev a l)
              ( weak-modal-logic-ax
                ( contains-ax-n _ (c , list-to-implications-rev a l , refl))))
            ( in-logic))
          ( weak-modal-logic-ax
            ( subtype-union-right logic
              ( pr1 x)
              ( □ c)
              ( sub c (unit-trunc-Prop (is-head c l))))))

    aux''' :
      (l : list (formula i)) →
      in-list l ⊆ (λ b → pr1 x (□ b)) →
      is-in-subtype (weak-modal-logic (union-subtype logic (in-list l))) (a) →
      is-in-subtype (weak-modal-logic (union-subtype logic (pr1 x))) (□ a)
    aux''' l sub in-logic =
      aux'''' l sub
        ( weak-modal-logic-ax
          ( subtype-union-left
            ( logic)
            ( pr1 x)
            ( □ (list-to-implications-rev a l))
            ( modal-logic-nec
              ( tr
                ( is-in-subtype logic)
                ( reverse-list-to-implications a l)
                ( subset-double-modal-logic
                  ( axioms)
                  ( list-to-implications a (reverse-list l))
                  ( weak-modal-logic-subset-modal-logic
                    ( logic)
                    ( list-to-implications a (reverse-list l))
                    ( move-right logic a (reverse-list l)
                      ( transitive-leq-subtype
                        ( ax-k i)
                        ( logic)
                        ( weak-modal-logic logic)
                        ( axioms-subset-weak-modal-logic logic)
                        ( contains-ax-k))
                      ( transitive-leq-subtype
                        ( ax-s i)
                        ( logic)
                        ( weak-modal-logic logic)
                        ( axioms-subset-weak-modal-logic logic)
                        ( contains-ax-s))
                      ( weak-modal-logic-monotic
                        ( subset-union-subset-right logic
                          ( in-list l)
                          ( in-list (reverse-list l))
                          ( subset-reversing-list l))
                        ( a)
                        ( in-logic)))))))))

    aux'' :
      (l : list (formula i)) →
      in-list l ⊆ (λ b → pr1 x (□ b)) →
      is-in-subtype
        ( weak-modal-logic
          ( theory-add-formula (~ a) (union-subtype logic (in-list l))))
        ( ⊥) →
      is-in-subtype (weak-modal-logic (union-subtype logic (pr1 x))) (□ a)
    aux'' l sub in-logic =
      aux''' l sub
        ( weak-modal-logic-mp
          { a = ~~ a}
          { b = a}
          ( weak-modal-logic-ax
            ( subtype-union-left logic
              ( in-list l)
              ( _)
              ( contains-ax-dn _ (a , refl))))
          ( forward-implication
            ( deduction-lemma
              ( union-subtype logic (in-list l))
                ( transitive-leq-subtype
                  ( ax-k i)
                  ( logic)
                  ( weak-modal-logic (union-subtype logic (in-list l)))
                  ( transitive-leq-subtype
                    ( logic)
                    ( union-subtype logic (in-list l))
                    ( weak-modal-logic (union-subtype logic (in-list l)))
                    ( axioms-subset-weak-modal-logic
                      ( union-subtype logic (in-list l)))
                    ( subtype-union-left logic (in-list l)))
                  ( contains-ax-k))
                ( transitive-leq-subtype
                  ( ax-s i)
                  ( logic)
                  ( weak-modal-logic (union-subtype logic (in-list l)))
                  ( transitive-leq-subtype
                    ( logic)
                    ( union-subtype logic (in-list l))
                    ( weak-modal-logic (union-subtype logic (in-list l)))
                    ( axioms-subset-weak-modal-logic
                      ( union-subtype logic (in-list l)))
                    ( subtype-union-left logic (in-list l)))
                  ( contains-ax-s))
              ( ~ a)
              ( ⊥))
            ( in-logic)))

    aux' :
      (l : list (formula i)) →
      in-list l ⊆ (λ b → pr1 x (□ b)) →
      is-in-subtype
        ( weak-modal-logic
          ( union-subtype logic (theory-add-formula (~ a) (in-list l))))
        ( ⊥) →
      is-in-subtype (weak-modal-logic (union-subtype logic (pr1 x))) (□ a)
    aux' l sub in-logic =
      aux'' l sub
        ( weak-modal-logic-monotic
          ( union-swap-1-2
            ( logic)
            ( Id-formula-Prop (~ a))
            ( in-list l))
          ( ⊥)
          ( in-logic))

    aux :
      (l : list (formula i)) →
      in-list l ⊆
        union-subtype logic (theory-add-formula (~ a) (λ b → pr1 x (□ b))) →
      is-in-subtype (weak-modal-logic (in-list l)) ⊥ →
      is-in-subtype (weak-modal-logic (union-subtype logic (pr1 x))) (□ a)
    aux l sub in-logic =
      apply-universal-property-trunc-Prop
        ( lists-in-union-lists l logic
          ( theory-add-formula (~ a) (λ b → pr1 x (□ b)))
          ( sub))
        ( weak-modal-logic (union-subtype logic (pr1 x)) (□ a))
        ( λ (l-ax , l-w , l-sub-union , l-ax-sub-axioms , l-w-sub-w) →
          ( apply-universal-property-trunc-Prop
            ( lists-in-union-lists l-w
              ( Id-formula-Prop (~ a))
              ( λ b → pr1 x (□ b))
              ( l-w-sub-w))
            ( weak-modal-logic (union-subtype logic (pr1 x)) (□ a))
            ( λ (l-not-a , l-boxes , l-sub-union' , l-not-a-sub , l-boxes-sub) →
              ( aux'
                ( l-boxes)
                ( l-boxes-sub)
                ( weak-modal-logic-monotic
                  { ax₁ = in-list l}
                  { ax₂ =
                    union-subtype logic
                      ( theory-add-formula (~ a) (in-list l-boxes))}
                  ( transitive-leq-subtype
                    ( in-list l)
                    ( union-subtype (in-list l-ax) (in-list l-w))
                    ( union-subtype
                      ( logic)
                      ( theory-add-formula (~ a) (in-list l-boxes)))
                    ( subset-union-subsets
                      ( in-list l-ax)
                      ( in-list l-w)
                      ( logic)
                      ( theory-add-formula (~ a) (in-list l-boxes))
                      ( l-ax-sub-axioms)
                      ( transitive-leq-subtype
                        ( in-list l-w)
                        ( union-subtype (in-list l-not-a) (in-list l-boxes))
                        ( theory-add-formula (~ a) (in-list l-boxes))
                        ( subset-union-subset-left
                          ( in-list l-not-a)
                          ( Id-formula-Prop (~ a))
                          ( in-list l-boxes)
                          ( l-not-a-sub))
                        ( l-sub-union')))
                    ( l-sub-union))
                  ( ⊥)
                  ( in-logic))))))

    w : is-in-subtype (pr1 x) (~ □ a) → L-consistent-theory
    pr1 (w b) = theory-add-formula (~ a) (λ b → pr1 x (□ b))
    pr2 (w not-box-in-logic) bot-in-logic =
      apply-universal-property-trunc-Prop
        ( bot-in-logic)
        ( empty-Prop)
        ( λ wd-bot →
          ( let (l , sub , wd) = list-assumptions-weak-deduction wd-bot
            in pr2 x
              ( weak-modal-logic-mp
                ( weak-modal-logic-ax
                  ( subtype-union-right logic (pr1 x) _ not-box-in-logic))
                ( aux l sub (unit-trunc-Prop wd)))))

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
            ( w-ax (subtype-union-right logic (pr1 x) ⊥ in-logic))))
    pr1 (canonical-model-theorem (a →ₘ b) x) in-logic fa =
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
    pr2 (canonical-model-theorem (a →ₘ b) x) f =
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
      complete-theory-box
        ( lem)
        ( pr1 x , pr1 (pr2 x))
        ( pr2 (pr2 x))
        ( a)
        ( λ y is-canonical access →
          ( backward-implication
            ( canonical-model-theorem a (y , is-canonical))
            ( f (y , is-canonical) access)))

    canonical-model-theorem' :
      (a : formula i) →
      neg-Prop (logic a) ⇔ neg-Prop (canonical-kripke-model ⊨M a)
    pr1 (canonical-model-theorem' a) nf in-logic =
      apply-universal-property-trunc-Prop
        ( lindenbaum x)
        ( empty-Prop)
        ( λ w →
          ( pr2 (pr1 w)
            ( weak-modal-logic-mp
              { a = a}
              ( weak-modal-logic-ax
                ( transitive-leq-subtype
                  ( theory-add-formula (~ a) logic)
                  ( pr1 (pr1 w))
                  ( union-subtype logic (pr1 (pr1 w)))
                  ( subtype-union-right logic (pr1 (pr1 w)))
                  ( pr1 (pr2 w))
                  ( ~ a)
                  ( formula-in-add-formula (~ a) logic)))
              ( weak-modal-logic-ax
                ( subtype-union-right
                  ( logic)
                  ( pr1 (pr1 w))
                  ( a)
                  ( backward-implication
                    ( canonical-model-theorem a
                      ( pr1 (pr1 w) , pr2 (pr1 w) , pr2 (pr2 w)))
                    ( in-logic
                      ( pr1 (pr1 w) , pr2 (pr1 w) , pr2 (pr2 w)))))))))
      where
      x : L-consistent-theory
      pr1 x = theory-add-formula (~ a) logic
      pr2 x bot-in-logic =
        nf
          ( modal-logic-mp
            { a = ~~ a}
            { b = a}
            ( contains-ax-dn _ (a , refl))
            ( subset-double-modal-logic
              ( axioms)
              ( ~~ a)
              ( weak-modal-logic-subset-modal-logic
                ( logic)
                ( ~~ a)
                ( forward-implication
                  ( deduction-lemma logic
                    ( transitive-leq-subtype
                      ( ax-k i)
                      ( logic)
                      ( weak-modal-logic logic)
                      ( axioms-subset-weak-modal-logic logic)
                      ( contains-ax-k))
                    ( transitive-leq-subtype
                      ( ax-s i)
                      ( logic)
                      ( weak-modal-logic logic)
                      ( axioms-subset-weak-modal-logic logic)
                      ( contains-ax-s))
                    ( ~ a)
                    ( ⊥))
                  ( weak-modal-logic-monotic
                    ( subtype-union-both
                      ( logic)
                      ( theory-add-formula (~ a) logic)
                      ( theory-add-formula (~ a) logic)
                      ( subtype-union-right (Id-formula-Prop (~ a)) logic)
                      ( refl-leq-subtype (theory-add-formula (~ a) logic)))
                    ( ⊥)
                    ( bot-in-logic))))))
    pr2 (canonical-model-theorem' a) =
      map-neg
        ( λ in-logic x →
          ( forward-implication
            ( canonical-model-theorem a x)
            ( logic-subset-L-complete-theory
              ( pr1 x , pr1 (pr2 x))
              ( pr2 (pr2 x))
              ( a)
              ( in-logic))))
```
