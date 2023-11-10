# Weak deduction

```agda
module modal-logic.weak-deduction where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.unions-subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import modal-logic.axioms
open import modal-logic.formulas
open import modal-logic.logic-syntax
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 l2 : Level} {i : Set l1}
  where

  infix 5 _▷_

  data _▷_ (axioms : formulas l2 i) : formula i → UU (l1 ⊔ l2) where
    w-ax : {a : formula i} → is-in-subtype axioms a → axioms ▷ a
    w-mp : {a b : formula i} → axioms ▷ a ⇒ b → axioms ▷ a → axioms ▷ b

  weak-modal-logic : formulas l2 i → formulas (l1 ⊔ l2) i
  weak-modal-logic axioms a = trunc-Prop (axioms ▷ a)

module _
  {l1 l2 : Level} {i : Set l1} (axioms : formulas l2 i)
  where

  deduction-weak-deduction : {a : formula i} → axioms ▷ a → axioms ⊢ a
  deduction-weak-deduction (w-ax x) = ax x
  deduction-weak-deduction (w-mp dab da) =
    mp (deduction-weak-deduction dab) (deduction-weak-deduction da)

  weak-modal-logic-subset-modal-logic :
    weak-modal-logic axioms ⊆ modal-logic axioms
  weak-modal-logic-subset-modal-logic a =
    map-universal-property-trunc-Prop
      ( modal-logic axioms a)
      ( unit-trunc-Prop ∘ deduction-weak-deduction)

module _
  {l1 l2 l3 : Level} {i : Set l1}
  {axioms₁ : formulas l2 i} {axioms₂ : formulas l3 i}
  (e : equiv-subtypes axioms₁ axioms₂)
  where

  deduction-equiv-axioms :
    {a : formula i} → axioms₁ ▷ a → axioms₂ ▷ a
  deduction-equiv-axioms {a} (w-ax x) =
    w-ax (map-equiv (e a) x)
  deduction-equiv-axioms (w-mp wdab wda) =
    w-mp (deduction-equiv-axioms wdab) (deduction-equiv-axioms wda)

module _
  {l1 : Level} {i : Set l1}
  where

  axioms-subset-weak-modal-logic :
    {l2 : Level} (axioms : formulas l2 i) → axioms ⊆ weak-modal-logic axioms
  axioms-subset-weak-modal-logic _ a H = unit-trunc-Prop (w-ax H)

  weak-modal-logic-closed :
    {l2 : Level} {axioms : formulas l2 i} {a : formula i} →
    weak-modal-logic axioms ▷ a →
    is-in-subtype (weak-modal-logic axioms) a
  weak-modal-logic-closed (w-ax x) = x
  weak-modal-logic-closed {axioms = axioms} {a} (w-mp tdab tda) =
    apply-twice-universal-property-trunc-Prop
      ( weak-modal-logic-closed tdab)
      ( weak-modal-logic-closed tda)
      ( weak-modal-logic axioms a)
      (λ dab da → unit-trunc-Prop (w-mp dab da))

  subset-double-weak-modal-logic :
    {l2 : Level}
    (axioms : formulas l2 i) →
    weak-modal-logic (weak-modal-logic axioms) ⊆ weak-modal-logic axioms
  subset-double-weak-modal-logic axioms a =
    map-universal-property-trunc-Prop
      ( weak-modal-logic axioms a)
      ( weak-modal-logic-closed)

  weak-modal-logic-idempotent :
    {l2 : Level}
    (axioms : formulas l2 i) →
    weak-modal-logic axioms ＝ weak-modal-logic (weak-modal-logic axioms)
  weak-modal-logic-idempotent axioms =
    antisymmetric-leq-subtype _ _
      ( axioms-subset-weak-modal-logic (weak-modal-logic axioms))
      ( subset-double-weak-modal-logic axioms)

module _
  {l1 l2 l3 : Level} {i : Set l1} {ax₁ : formulas l2 i} {ax₂ : formulas l3 i}
  (leq : ax₁ ⊆ ax₂)
  where

  weak-deduction-monotic : {a : formula i} → ax₁ ▷ a → ax₂ ▷ a
  weak-deduction-monotic (w-ax x) = w-ax (leq _ x)
  weak-deduction-monotic (w-mp wdab wda) =
    w-mp (weak-deduction-monotic wdab) (weak-deduction-monotic wda)

  weak-modal-logic-monotic : weak-modal-logic ax₁ ⊆ weak-modal-logic ax₂
  weak-modal-logic-monotic a =
    map-universal-property-trunc-Prop
      ( weak-modal-logic ax₂ a)
      ( unit-trunc-Prop ∘ weak-deduction-monotic)

module _
  {l1 l2 l3 : Level} {i : Set l1} {ax₁ : formulas l2 i} {ax₂ : formulas l3 i}
  where

  subset-weak-modal-logic-if-subset-axioms :
    ax₁ ⊆ weak-modal-logic ax₂ → weak-modal-logic ax₁ ⊆ weak-modal-logic ax₂
  subset-weak-modal-logic-if-subset-axioms leq =
    transitive-leq-subtype
      ( weak-modal-logic ax₁)
      ( weak-modal-logic (weak-modal-logic ax₂))
      ( weak-modal-logic ax₂)
      ( subset-double-weak-modal-logic ax₂)
      ( weak-modal-logic-monotic leq)

module _
  {l1 l2 : Level} {i : Set l1} (axioms : formulas l2 i)
  where

  backward-deduction-lemma :
    {a b : formula i} →
    axioms ▷ a ⇒ b →
    is-in-subtype (weak-modal-logic (theory-add-formula a axioms)) (b)
  backward-deduction-lemma {a} wab =
    unit-trunc-Prop
      ( w-mp
        ( weak-deduction-monotic
          ( subtype-union-right ((Id-formula-Prop a)) axioms) wab)
        ( w-ax (subtype-union-left (Id-formula-Prop a) axioms a refl)))

  module _
    -- TODO: maybe just in axioms?
    (contains-ax-k : ax-k i ⊆ weak-modal-logic axioms)
    (contains-ax-s : ax-s i ⊆ weak-modal-logic axioms)
    where

    deduction-a->a :
      (a : formula i) → is-in-subtype (weak-modal-logic axioms) (a ⇒ a)
    deduction-a->a a =
      apply-three-times-universal-property-trunc-Prop
        ( contains-ax-s _ (a , a ⇒ a , a , refl))
        ( contains-ax-k _ (a , a ⇒ a , refl))
        ( contains-ax-k _ (a , a , refl))
        ( (weak-modal-logic axioms) (a ⇒ a))
        ( λ x y z → unit-trunc-Prop (w-mp (w-mp x y) z))

    forward-deduction-lemma :
      (a : formula i) {b : formula i} →
      theory-add-formula a axioms ▷ b →
      is-in-subtype (weak-modal-logic axioms) (a ⇒ b)
    forward-deduction-lemma a {b} (w-ax x) =
      elim-disj-Prop
        ( Id-formula-Prop a b)
        ( axioms b)
        ( (weak-modal-logic axioms) (a ⇒ b))
        ( (λ { refl → deduction-a->a a})
        , (λ in-axioms →
            ( apply-universal-property-trunc-Prop
              ( contains-ax-k _ (b , a , refl))
              ( (weak-modal-logic axioms) (a ⇒ b))
              ( λ x → unit-trunc-Prop (w-mp x (w-ax in-axioms))))))
        ( x)
    forward-deduction-lemma a {b} (w-mp {c} twdcb twdc) =
      apply-three-times-universal-property-trunc-Prop
        ( forward-deduction-lemma a twdcb)
        ( forward-deduction-lemma a twdc)
        ( contains-ax-s _ (a , c , b , refl))
        ( (weak-modal-logic axioms) (a ⇒ b))
        ( λ wdacb wdac x →
          ( unit-trunc-Prop (w-mp (w-mp x wdacb) wdac)))

    deduction-lemma :
      (a b : formula i) →
      weak-modal-logic (theory-add-formula a axioms) b ⇔
        weak-modal-logic axioms (a ⇒ b)
    pr1 (deduction-lemma a b) =
      map-universal-property-trunc-Prop
        ( (weak-modal-logic axioms) (a ⇒ b))
        ( forward-deduction-lemma a)
    pr2 (deduction-lemma a b) =
      map-universal-property-trunc-Prop
        ( weak-modal-logic (theory-add-formula a axioms) b)
        ( backward-deduction-lemma)

module _
  {l1 l2 : Level} {i : Set l1} (axioms : formulas l2 i)
  (contains-ax-k : ax-k i ⊆ weak-modal-logic axioms)
  (contains-ax-s : ax-s i ⊆ weak-modal-logic axioms)
  (contains-ax-dn : ax-dn i ⊆ weak-modal-logic axioms)
  where

    deduction-ex-falso :
      (a b : formula i) →
      is-in-subtype (weak-modal-logic axioms) (~ a ⇒ a ⇒ b)
    deduction-ex-falso a b =
      forward-implication
        ( deduction-lemma axioms contains-ax-k contains-ax-s (~ a) (a ⇒ b))
        ( forward-implication
          ( deduction-lemma
            ( theory-add-formula (~ a) axioms)
            ( transitive-leq-subtype
              ( ax-k i)
              ( weak-modal-logic axioms)
              ( weak-modal-logic (theory-add-formula (a ⇒ ⊥) axioms))
              ( weak-modal-logic-monotic
                ( subtype-union-right (Id-formula-Prop (~ a)) axioms))
              ( contains-ax-k))
            ( transitive-leq-subtype
              ( ax-s i)
              ( weak-modal-logic axioms)
              ( weak-modal-logic (theory-add-formula (a ⇒ ⊥) axioms))
              ( weak-modal-logic-monotic
                ( subtype-union-right (Id-formula-Prop (~ a)) axioms))
              ( contains-ax-s))
            ( a)
            ( b))
          ( apply-twice-universal-property-trunc-Prop
            ( contains-ax-k _ (⊥ , ~ b , refl))
            ( contains-ax-dn _ ((b , refl)))
            ( weak-modal-logic
              ( theory-add-formula a (theory-add-formula (~ a) axioms)) b)
            ( λ x y →
              ( unit-trunc-Prop
                ( w-mp {a = ~~ b}
                  ( weak-deduction-monotic
                    ( transitive-leq-subtype
                      ( axioms)
                      ( theory-add-formula (~ a) axioms)
                      ( theory-add-formula a
                        ( theory-add-formula (~ a) axioms))
                      ( subtype-union-right
                        ( Id-formula-Prop a)
                        ( theory-add-formula (~ a) axioms))
                      ( subtype-union-right (Id-formula-Prop (~ a)) axioms))
                    ( y))
                  ( w-mp {a = ⊥}
                    ( weak-deduction-monotic
                      ( transitive-leq-subtype
                        ( axioms)
                        ( theory-add-formula (~ a) axioms)
                        ( theory-add-formula a
                          ( theory-add-formula (~ a) axioms))
                        ( subtype-union-right
                          ( Id-formula-Prop a)
                          ( theory-add-formula (~ a) axioms))
                        ( subtype-union-right (Id-formula-Prop (~ a)) axioms))
                      ( x))
                    ( w-mp {a = a}
                      ( w-ax
                        ( unit-trunc-Prop (inr (unit-trunc-Prop (inl refl)))))
                      ( w-ax (unit-trunc-Prop (inl refl))))))))))

    logic-ex-falso :
      (a b : formula i) →
      is-in-subtype (weak-modal-logic axioms) a →
      is-in-subtype (weak-modal-logic axioms) (~ a) →
      is-in-subtype (weak-modal-logic axioms) b
    logic-ex-falso a b a-in-logic not-a-in-logic =
      apply-three-times-universal-property-trunc-Prop
        ( a-in-logic)
        ( not-a-in-logic)
        ( deduction-ex-falso a b)
        ( (weak-modal-logic axioms) b)
        ( λ x y z → unit-trunc-Prop (w-mp (w-mp z y) x))
```
