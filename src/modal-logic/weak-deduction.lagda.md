# Weak deduction

```agda
module modal-logic.weak-deduction where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
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

open import foundation-core.negation

open import lists.concatenation-lists
open import lists.lists
open import lists.reversing-lists

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
  {l1 l2 : Level} {i : Set l1} {axioms : formulas l2 i}
  where

  weak-modal-logic-ax :
    {a : formula i} →
    is-in-subtype axioms a →
    is-in-subtype (weak-modal-logic axioms) a
  weak-modal-logic-ax = unit-trunc-Prop ∘ w-ax

  weak-modal-logic-mp :
    {a b : formula i} →
    is-in-subtype (weak-modal-logic axioms) (a ⇒ b) →
    is-in-subtype (weak-modal-logic axioms) a →
    is-in-subtype (weak-modal-logic axioms) b
  weak-modal-logic-mp {a} {b} twdab twda =
    apply-twice-universal-property-trunc-Prop twdab twda
      ( weak-modal-logic axioms b)
      ( λ wdab wda → unit-trunc-Prop (w-mp wdab wda))

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

-- TODO: move to lists

in-list : {l : Level} {A : UU l} → list A → A → Prop l
in-list l a = trunc-Prop (a ∈-list l)

subset-in-tail :
  {l : Level} {A : UU l} (a : A) (l : list A) →
  in-list l ⊆ in-list (cons a l)
subset-in-tail a l x =
  map-universal-property-trunc-Prop
    ( in-list (cons a l) x)
    ( unit-trunc-Prop ∘ (is-in-tail x a l))

in-concat-list :
  {l : Level} {A : UU l} (l1 l2 : list A) →
  (a : A) → a ∈-list (concat-list l1 l2) → (a ∈-list l1) + (a ∈-list l2)
in-concat-list nil l2 a in-list = inr in-list
in-concat-list (cons x l1) l2 a (is-head a _) = inl (is-head a l1)
in-concat-list (cons x l1) l2 a (is-in-tail _ _ _ in-tail)
  with in-concat-list l1 l2 a in-tail
... | inl in-l1 = inl (is-in-tail a x l1 in-l1)
... | inr in-l2 = inr in-l2

subset-reversing-list :
  {l : Level} {A : UU l} (l : list A) → in-list l ⊆ in-list (reverse-list l)
subset-reversing-list l x =
  map-universal-property-trunc-Prop
    ( in-list (reverse-list l) x)
    ( unit-trunc-Prop ∘ forward-contains-reverse-list x l)

in-sum-concat-list-Prop :
  {l : Level} {A : UU l} (l1 l2 : list A) →
  (a : A) → a ∈-list (concat-list l1 l2) →
  type-Prop (in-list l1 a) + type-Prop (in-list l2 a)
in-sum-concat-list-Prop l1 l2 a in-concat with in-concat-list l1 l2 a in-concat
... | inl in-l1 = inl (unit-trunc-Prop in-l1)
... | inr in-l2 = inr (unit-trunc-Prop in-l2)

union-lists-concat :
  {l : Level} {A : UU l} (l1 l2 : list A) →
  in-list (concat-list l1 l2) ⊆ union-subtype (in-list l1) (in-list l2)
union-lists-concat l1 l2 a =
  map-universal-property-trunc-Prop
    ( union-subtype (in-list l1) (in-list l2) a)
    ( unit-trunc-Prop ∘ (in-sum-concat-list-Prop l1 l2 a))

in-concat-left :
  {l : Level} {A : UU l} (l1 l2 : list A)
  {a : A} → a ∈-list l1 → a ∈-list (concat-list l1 l2)
in-concat-left _ _ (is-head a _) =
  is-head a _
in-concat-left _ l2 (is-in-tail a x l1 in-l1) =
  is-in-tail a x (concat-list l1 l2) (in-concat-left l1 l2 in-l1)

in-concat-right :
  {l : Level} {A : UU l} (l1 l2 : list A)
  {a : A} → a ∈-list l2 → a ∈-list (concat-list l1 l2)
in-concat-right nil l2 in-l2 = in-l2
in-concat-right (cons x l1) l2 in-l2 =
  is-in-tail _ x (concat-list l1 l2) (in-concat-right l1 l2 in-l2)

in-concat-list-sum-Prop :
  {l : Level} {A : UU l} (l1 l2 : list A) →
  (a : A) → type-Prop (in-list l1 a) + type-Prop (in-list l2 a) →
  type-Prop (in-list (concat-list l1 l2) a)
in-concat-list-sum-Prop l1 l2 a (inl in-l1) =
  apply-universal-property-trunc-Prop
    ( in-l1)
    ( in-list (concat-list l1 l2) a)
    ( unit-trunc-Prop ∘ (in-concat-left l1 l2))
in-concat-list-sum-Prop l1 l2 a (inr in-l2) =
  apply-universal-property-trunc-Prop
    ( in-l2)
    ( in-list (concat-list l1 l2) a)
    ( unit-trunc-Prop ∘ (in-concat-right l1 l2))

in-concat-lists-union :
  {l : Level} {A : UU l} (l1 l2 : list A) →
  union-subtype (in-list l1) (in-list l2) ⊆ in-list (concat-list l1 l2)
in-concat-lists-union l1 l2 a =
  map-universal-property-trunc-Prop
    ( in-list (concat-list l1 l2) a)
    ( in-concat-list-sum-Prop l1 l2 a)

empty-in-list-nil :
  {l : Level} {A : UU l} {x : A} → is-in-subtype (in-list nil) x → empty
empty-in-list-nil = map-universal-property-trunc-Prop empty-Prop ( λ ())

equiv-subset-head-tail :
  {l1 l2 : Level} {A : UU l1} (x : A) (xs : list A) (a : subtype l2 A) →
  (leq-prop-subtype (in-list (cons x xs)) a) ⇔
    prod-Prop (a x) (leq-prop-subtype (in-list xs) a)
pr1 (equiv-subset-head-tail x xs a) sub =
  pair
    ( sub x (unit-trunc-Prop (is-head x xs)))
    ( transitive-leq-subtype
      ( in-list xs)
      ( in-list (cons x xs))
      ( a)
      ( sub)
      ( subset-in-tail x xs))
pr2 (equiv-subset-head-tail x xs a) (x-in-a , sub) y =
  map-universal-property-trunc-Prop
    ( a y)
    ( λ
      { (is-head .x .xs) → x-in-a
      ; (is-in-tail .y .x .xs y-in-list) → sub y (unit-trunc-Prop y-in-list)})

lists-in-union-lists :
  {l1 l2 l3 : Level} {A : UU l1}
  (xs : list A) (a : subtype l2 A) (b : subtype l3 A) →
  in-list xs ⊆ union-subtype a b →
  ∃
    ( list A)
    ( λ xsl →
      ( Σ
        ( list A)
        ( λ xsr →
          ( in-list xs ⊆ union-subtype (in-list xsl) (in-list xsr)) ×
          ( in-list xsl ⊆ a) ×
          ( in-list xsr ⊆ b))))
lists-in-union-lists nil a b sub =
  unit-trunc-Prop
    ( triple nil nil
      ( triple
        ( λ _ → ex-falso ∘ empty-in-list-nil)
        ( λ _ → ex-falso ∘ empty-in-list-nil)
        ( λ _ → ex-falso ∘ empty-in-list-nil)))
lists-in-union-lists (cons x xs) a b sub =
  apply-twice-universal-property-trunc-Prop
    ( lists-in-union-lists xs a b
      ( transitive-leq-subtype
        ( in-list xs)
        ( in-list (cons x xs))
        ( union-subtype a b)
        ( sub)
        ( subset-in-tail x xs)))
    ( sub x (unit-trunc-Prop (is-head x xs)))
    ( ∃-Prop _ (λ _ → Σ _ _))
    ( λ (xsl , xsr , sub-lists , sub-xsl , sub-xsr) →
      ( ind-coprod
        ( λ _ → _)
        ( λ x-in-a →
          ( unit-trunc-Prop
            ( triple (cons x xsl) xsr
              ( triple
                ( λ y →
                  ( map-universal-property-trunc-Prop
                    ( union-subtype (in-list (cons x xsl)) (in-list xsr) y)
                    ( λ
                      { (is-head .x .xs) →
                        ( subtype-union-left
                          ( in-list (cons x xsl))
                          ( in-list xsr)
                          ( y)
                          ( unit-trunc-Prop (is-head y xsl)))
                      ; (is-in-tail .y .x .xs y-in-xs) →
                        ( subset-union-subset-left
                          ( in-list xsl)
                          ( in-list (cons x xsl))
                          ( in-list xsr)
                          ( subset-in-tail x xsl)
                          ( y)
                          ( sub-lists y (unit-trunc-Prop y-in-xs)))})))
                ( backward-implication
                  ( equiv-subset-head-tail x xsl a)
                  ( x-in-a , sub-xsl))
                ( sub-xsr)))))
        ( λ x-in-b →
          ( unit-trunc-Prop
            ( triple xsl (cons x xsr)
              ( triple
                ( λ y →
                  ( map-universal-property-trunc-Prop
                    ( union-subtype (in-list xsl) (in-list (cons x xsr)) y)
                    ( λ
                      { (is-head .x .xs) →
                        ( subtype-union-right
                          ( in-list xsl)
                          ( in-list (cons x xsr))
                          ( y)
                          ( unit-trunc-Prop (is-head y xsr)))
                      ; (is-in-tail .y .x .xs y-in-xs) →
                        ( subset-union-subset-right
                          ( in-list xsl)
                          ( in-list xsr)
                          ( in-list (cons x xsr))
                          ( subset-in-tail x xsr)
                          ( y)
                          ( sub-lists y (unit-trunc-Prop y-in-xs)))})))
                ( sub-xsl)
                ( backward-implication
                  ( equiv-subset-head-tail x xsr b)
                  ( x-in-b , sub-xsr))))))))

module _
  {l1 : Level} {i : Set l1}
  where

  list-assumptions-weak-deduction :
    {l2 : Level} {logic : formulas l2 i} {a : formula i} →
    logic ▷ a →
    Σ (list (formula i)) (λ l → (in-list l ⊆ logic) × (in-list l ▷ a))
  pr1 (list-assumptions-weak-deduction {a = a} (w-ax x)) =
    unit-list a
  pr1 (pr2 (list-assumptions-weak-deduction {logic = logic} (w-ax x))) b =
    map-universal-property-trunc-Prop ( logic b) ( λ { (is-head _ _) → x})
  pr2 (pr2 (list-assumptions-weak-deduction {a = a} (w-ax x))) =
    w-ax (unit-trunc-Prop (is-head a nil))
  pr1 (list-assumptions-weak-deduction (w-mp wdcb wdc)) =
    concat-list
      ( pr1 (list-assumptions-weak-deduction wdcb))
      ( pr1 (list-assumptions-weak-deduction wdc))
  pr1 (pr2 (list-assumptions-weak-deduction {logic = logic} (w-mp wdcb wdc)))
    b b-in-list =
    subtype-union-both
      ( in-list (pr1 (list-assumptions-weak-deduction wdcb)))
      ( in-list (pr1 (list-assumptions-weak-deduction wdc)))
      ( logic)
      ( pr1 (pr2 (list-assumptions-weak-deduction wdcb)))
      ( pr1 (pr2 (list-assumptions-weak-deduction wdc)))
      ( b)
      ( union-lists-concat
        ( pr1 (list-assumptions-weak-deduction wdcb))
        ( pr1 (list-assumptions-weak-deduction wdc))
        ( b)
        ( b-in-list))
  pr2 (pr2 (list-assumptions-weak-deduction (w-mp wdcb wdc))) =
    w-mp
      ( weak-deduction-monotic
        ( transitive-leq-subtype
          ( in-list (pr1 (list-assumptions-weak-deduction wdcb)))
          ( union-subtype
            ( in-list (pr1 (list-assumptions-weak-deduction wdcb)))
            ( in-list (pr1 (list-assumptions-weak-deduction wdc))))
          ( in-list
            ( concat-list
              ( pr1 (list-assumptions-weak-deduction wdcb))
              ( pr1 (list-assumptions-weak-deduction wdc))))
          ( in-concat-lists-union
            ( pr1 (list-assumptions-weak-deduction wdcb))
            ( pr1 (list-assumptions-weak-deduction wdc)))
          ( subtype-union-left
            ( in-list (pr1 (list-assumptions-weak-deduction wdcb)))
            ( in-list (pr1 (list-assumptions-weak-deduction wdc)))))
        ( pr2 (pr2 (list-assumptions-weak-deduction wdcb))))
      ( weak-deduction-monotic
        ( transitive-leq-subtype
          ( in-list (pr1 (list-assumptions-weak-deduction wdc)))
          ( union-subtype
            ( in-list (pr1 (list-assumptions-weak-deduction wdcb)))
            ( in-list (pr1 (list-assumptions-weak-deduction wdc))))
          ( in-list
            ( concat-list
              ( pr1 (list-assumptions-weak-deduction wdcb))
              ( pr1 (list-assumptions-weak-deduction wdc))))
          ( in-concat-lists-union
            ( pr1 (list-assumptions-weak-deduction wdcb))
            ( pr1 (list-assumptions-weak-deduction wdc)))
          ( subtype-union-right
            ( in-list (pr1 (list-assumptions-weak-deduction wdcb)))
            ( in-list (pr1 (list-assumptions-weak-deduction wdc)))))
        ( pr2 (pr2 (list-assumptions-weak-deduction wdc))))

  nil-no-deduction : {a : formula i} → ¬ (in-list nil ▷ a)
  nil-no-deduction (w-ax x) =
    apply-universal-property-trunc-Prop x empty-Prop (λ ())
  nil-no-deduction (w-mp wd _) = nil-no-deduction wd

  -- list-assumptions-weak-modal-logic :
  --   {l2 : Level} {logic : formulas l2 i} {a : formula i} →
  --   is-in-subtype (weak-modal-logic logic) a →
  --   ∃ ( list (formula i))
  --     ( λ l →
  --       ( in-list l ⊆ logic) ×
  --       ( is-in-subtype (weak-modal-logic (in-list l)) a))
  -- list-assumptions-weak-modal-logic {l2} {logic} {a} =
  --   map-universal-property-trunc-Prop
  --     ( ∃-Prop
  --       ( list (formula i))
  --       ( λ l →
  --         ( in-list l ⊆ logic) ×
  --         ( is-in-subtype (weak-modal-logic (in-list l)) a)) )
  --     ( λ wda →
  --       ( let (l , sub , comp) = list-assumptions-weak-deduction wda
  --         in unit-trunc-Prop (l , sub , (unit-trunc-Prop comp))))

  forward-subset-head-add :
    (a : formula i) (l : list (formula i)) →
    theory-add-formula a (in-list l) ⊆ in-list (cons a l)
  forward-subset-head-add a l =
    subtype-union-both
      ( Id-formula-Prop a)
      ( in-list l)
      ( in-list (cons a l))
      ( λ { .a refl → unit-trunc-Prop (is-head a l)})
      ( subset-in-tail a l)

  backward-subset-head-add :
    (a : formula i) (l : list (formula i)) →
    in-list (cons a l) ⊆ theory-add-formula a (in-list l)
  backward-subset-head-add a l x =
    map-universal-property-trunc-Prop
      ( theory-add-formula a (in-list l) x)
      ( λ
        { (is-head .a .l) →
          ( subtype-union-left (Id-formula-Prop a) (in-list l) a refl)
        ; (is-in-tail .x .a .l t) →
          ( subtype-union-right
            ( Id-formula-Prop a)
            ( in-list l)
            ( x)
            ( unit-trunc-Prop t))})

module _
  {l1 l2 : Level} {i : Set l1} (axioms : formulas l2 i)
  where

  backward-deduction-lemma :
    {a b : formula i} →
    axioms ▷ a ⇒ b →
    is-in-subtype (weak-modal-logic (theory-add-formula a axioms)) b
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
