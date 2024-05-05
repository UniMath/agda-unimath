# Weak deduction

```agda
module modal-logic.weak-deduction where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.conjunction
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
open import lists.lists-subtypes
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

  is-weak-deduction-Prop :
    {axioms : modal-theory l2 i} {a : formula i} → axioms ⊢ a → Prop lzero
  is-weak-deduction-Prop (ax x) = unit-Prop
  is-weak-deduction-Prop (mp dab da) =
    conjunction-Prop (is-weak-deduction-Prop dab) (is-weak-deduction-Prop da)
  is-weak-deduction-Prop (nec d) = empty-Prop

  is-weak-deduction :
    {axioms : modal-theory l2 i} {a : formula i} → axioms ⊢ a → UU lzero
  is-weak-deduction = type-Prop ∘ is-weak-deduction-Prop

  infix 5 _⊢w_

  _⊢w_ : modal-theory l2 i → formula i → UU (l1 ⊔ l2)
  axioms ⊢w a = type-subtype (is-weak-deduction-Prop {axioms} {a})

  deduction-weak-deduction :
    {axioms : modal-theory l2 i} {a : formula i} → axioms ⊢w a → axioms ⊢ a
  deduction-weak-deduction = inclusion-subtype is-weak-deduction-Prop

  is-weak-deduction-deduction-weak-deduction :
    {axioms : modal-theory l2 i} {a : formula i} (d : axioms ⊢w a) →
    is-weak-deduction (deduction-weak-deduction d)
  is-weak-deduction-deduction-weak-deduction =
    is-in-subtype-inclusion-subtype is-weak-deduction-Prop

  weak-deduction-ax :
    {axioms : modal-theory l2 i} {a : formula i} →
    is-in-subtype axioms a →
    axioms ⊢w a
  weak-deduction-ax in-axioms = ax in-axioms , star

  weak-deduction-mp :
    {axioms : modal-theory l2 i} {a b : formula i} →
    axioms ⊢w (a →ₘ b) →
    axioms ⊢w a →
    axioms ⊢w b
  weak-deduction-mp (dab , is-w-dab) (da , is-w-da) =
    mp dab da , is-w-dab , is-w-da

  ind-weak-deduction :
    {l : Level} {axioms : modal-theory l2 i}
    (P : {a : formula i} → axioms ⊢w a → UU l) →
    ( {a : formula i} (in-axioms : is-in-subtype axioms a) →
      P (weak-deduction-ax in-axioms)) →
    ( {a b : formula i} (dab : axioms ⊢w a →ₘ b) (da : axioms ⊢w a) →
      P dab → P da → P (weak-deduction-mp dab da)) →
    {a : formula i} (wd : axioms ⊢w a) → P wd
  ind-weak-deduction P H-ax H-mp (ax in-axioms , _) =
    H-ax in-axioms
  ind-weak-deduction P H-ax H-mp (mp dba db , is-w-dba , is-w-db) =
    H-mp _ _
      ( ind-weak-deduction P H-ax H-mp (dba , is-w-dba))
      ( ind-weak-deduction P H-ax H-mp (db , is-w-db))

  rec-weak-deduction :
    {l : Level} {axioms : modal-theory l2 i} {P : UU l} →
    ( {a : formula i} (in-axioms : is-in-subtype axioms a) → P) →
    ( {a b : formula i} (dab : axioms ⊢w a →ₘ b) (da : axioms ⊢w a) →
      P → P → P) →
    {a : formula i} (wd : axioms ⊢w a) → P
  rec-weak-deduction {P = P} = ind-weak-deduction (λ _ → P)

  weak-modal-logic-closure : modal-theory l2 i → modal-theory (l1 ⊔ l2) i
  weak-modal-logic-closure axioms a = trunc-Prop (axioms ⊢w a)

  is-weak-modal-logic-Prop : modal-theory l2 i → Prop (l1 ⊔ l2)
  is-weak-modal-logic-Prop theory =
    leq-prop-subtype (weak-modal-logic-closure theory) theory

  is-weak-modal-logic : modal-theory l2 i → UU (l1 ⊔ l2)
  is-weak-modal-logic = type-Prop ∘ is-weak-modal-logic-Prop

  is-in-weak-modal-logic-closure-weak-deduction :
    {axioms : modal-theory l2 i} {a : formula i} →
    axioms ⊢w a → is-in-subtype (weak-modal-logic-closure axioms) a
  is-in-weak-modal-logic-closure-weak-deduction = unit-trunc-Prop

  subset-weak-modal-logic-closure-modal-logic-closure :
    {axioms : modal-theory l2 i} →
    weak-modal-logic-closure axioms ⊆ modal-logic-closure axioms
  subset-weak-modal-logic-closure-modal-logic-closure {axioms} a =
    map-universal-property-trunc-Prop
      ( modal-logic-closure axioms a)
      ( is-in-modal-logic-closure-deduction ∘ deduction-weak-deduction)

  is-weak-modal-logic-is-modal-logic :
    {theory : modal-theory l2 i} →
    is-modal-logic theory →
    is-weak-modal-logic theory
  is-weak-modal-logic-is-modal-logic {theory} is-m =
    transitive-leq-subtype
      ( weak-modal-logic-closure theory)
      ( modal-logic-closure theory)
      ( theory)
      ( is-m)
      ( subset-weak-modal-logic-closure-modal-logic-closure)

module _
  {l1 l2 : Level} {i : Set l1} {axioms : modal-theory l2 i}
  where

  weak-modal-logic-closure-ax :
    {a : formula i} →
    is-in-subtype axioms a →
    is-in-subtype (weak-modal-logic-closure axioms) a
  weak-modal-logic-closure-ax =
    is-in-weak-modal-logic-closure-weak-deduction ∘ weak-deduction-ax

  weak-modal-logic-closure-mp :
    {a b : formula i} →
    is-in-subtype (weak-modal-logic-closure axioms) (a →ₘ b) →
    is-in-subtype (weak-modal-logic-closure axioms) a →
    is-in-subtype (weak-modal-logic-closure axioms) b
  weak-modal-logic-closure-mp {a} {b} twdab twda =
    apply-twice-universal-property-trunc-Prop twdab twda
      ( weak-modal-logic-closure axioms b)
      ( λ wdab wda →
        ( is-in-weak-modal-logic-closure-weak-deduction
          ( weak-deduction-mp wdab wda)))

module _
  {l1 l2 : Level} {i : Set l1}
  {theory : modal-theory l2 i}
  (is-w : is-weak-modal-logic theory)
  where

  weak-modal-logic-mp :
    {a b : formula i} →
    is-in-subtype theory (a →ₘ b) →
    is-in-subtype theory a →
    is-in-subtype theory b
  weak-modal-logic-mp {a} {b} dab da =
    is-w b
      ( weak-modal-logic-closure-mp
        ( weak-modal-logic-closure-ax dab)
        ( weak-modal-logic-closure-ax da))

module _
  {l1 l2 : Level} {i : Set l1} {axioms : modal-theory l2 i}
  where

  weak-modal-logic-closed :
    {a : formula i} → weak-modal-logic-closure axioms ⊢w a →
    is-in-subtype (weak-modal-logic-closure axioms) a
  weak-modal-logic-closed =
    ind-weak-deduction _
      ( λ in-axioms → in-axioms)
      ( λ _ _ in-logic-ab in-logic-a →
        ( weak-modal-logic-closure-mp in-logic-ab in-logic-a))

  is-weak-modal-logic-weak-modal-logic-closure :
    is-weak-modal-logic (weak-modal-logic-closure axioms)
  is-weak-modal-logic-weak-modal-logic-closure a =
    map-universal-property-trunc-Prop
      ( weak-modal-logic-closure axioms a)
      ( weak-modal-logic-closed)

  subset-axioms-weak-modal-logic-closure :
    axioms ⊆ weak-modal-logic-closure axioms
  subset-axioms-weak-modal-logic-closure a = weak-modal-logic-closure-ax

module _
  {l1 l2 l3 : Level} {i : Set l1}
  {ax₁ : modal-theory l2 i}
  {ax₂ : modal-theory l3 i}
  (leq : ax₁ ⊆ ax₂)
  where

  weak-deduction-monotic : {a : formula i} → ax₁ ⊢w a → ax₂ ⊢w a
  weak-deduction-monotic =
    ind-weak-deduction _
      ( λ {a} in-axioms → weak-deduction-ax (leq a in-axioms))
      ( λ _ _ dab da → weak-deduction-mp dab da)

  weak-modal-logic-closure-monotic :
    weak-modal-logic-closure ax₁ ⊆ weak-modal-logic-closure ax₂
  weak-modal-logic-closure-monotic a =
    map-universal-property-trunc-Prop
      ( weak-modal-logic-closure ax₂ a)
      ( is-in-weak-modal-logic-closure-weak-deduction ∘ weak-deduction-monotic)

module _
  {l1 l2 l3 : Level} {i : Set l1}
  {ax₁ : modal-theory l2 i}
  {ax₂ : modal-theory l3 i}
  where

  subset-weak-modal-logic-subset-axioms :
    ax₁ ⊆ weak-modal-logic-closure ax₂ →
    weak-modal-logic-closure ax₁ ⊆ weak-modal-logic-closure ax₂
  subset-weak-modal-logic-subset-axioms leq =
    transitive-leq-subtype
      ( weak-modal-logic-closure ax₁)
      ( weak-modal-logic-closure (weak-modal-logic-closure ax₂))
      ( weak-modal-logic-closure ax₂)
      ( is-weak-modal-logic-weak-modal-logic-closure)
      ( weak-modal-logic-closure-monotic leq)

module _
  {l1 : Level} {i : Set l1}
  where

  backward-subset-head-add :
    (a : formula i) (l : list (formula i)) →
    list-subtype (cons a l) ⊆ theory-add-formula a (list-subtype l)
  backward-subset-head-add a l =
    subset-list-subtype-cons
      ( theory-add-formula a (list-subtype l))
      ( formula-in-add-formula a (list-subtype l))
      ( subset-add-formula a (list-subtype l))

module _
  {l1 l2 : Level} {i : Set l1}
  (axioms : modal-theory l2 i)
  where

  backward-deduction-lemma :
    {a b : formula i} →
    axioms ⊢w a →ₘ b →
    theory-add-formula a axioms ⊢w b
  backward-deduction-lemma {a} wab =
    weak-deduction-mp
      ( weak-deduction-monotic
        ( subset-add-formula a axioms)
        ( wab))
      ( weak-deduction-ax (formula-in-add-formula a axioms))

  module _
    (contains-ax-k : ax-k i ⊆ axioms)
    (contains-ax-s : ax-s i ⊆ axioms)
    where

    -- TODO: move to file with deduction
    deduction-a->a :
      (a : formula i) → axioms ⊢w a →ₘ a
    deduction-a->a a =
      weak-deduction-mp
        ( weak-deduction-mp
          ( weak-deduction-ax (contains-ax-s _ (a , a →ₘ a , a , refl)))
          ( weak-deduction-ax (contains-ax-k _ (a , a →ₘ a , refl))))
        ( weak-deduction-ax (contains-ax-k _ (a , a , refl)))

    forward-deduction-lemma :
      (a : formula i) {b : formula i} →
      theory-add-formula a axioms ⊢w b →
      is-in-subtype (weak-modal-logic-closure axioms) (a →ₘ b)
    forward-deduction-lemma a =
      ind-weak-deduction _
        ( λ {b} b-in-axioms →
          ( elim-theory-add-formula a axioms
            ( λ x → weak-modal-logic-closure axioms (a →ₘ x))
            ( is-in-weak-modal-logic-closure-weak-deduction (deduction-a->a a))
            ( λ x x-in-axioms →
              ( weak-modal-logic-closure-mp
                ( weak-modal-logic-closure-ax
                  ( contains-ax-k (x →ₘ a →ₘ x) (x , a , refl)))
                ( weak-modal-logic-closure-ax x-in-axioms)))
            ( b)
            ( b-in-axioms)))
        ( λ {b} {c} _ _ dabc dab →
          ( weak-modal-logic-closure-mp
            ( weak-modal-logic-closure-mp
              ( weak-modal-logic-closure-ax
                ( contains-ax-s _ (a , b , c , refl)))
              ( dabc))
            ( dab)))

    deduction-lemma :
      (a b : formula i) →
      type-iff-Prop
        ( weak-modal-logic-closure (theory-add-formula a axioms) b)
        ( weak-modal-logic-closure axioms (a →ₘ b))
    pr1 (deduction-lemma a b) =
      map-universal-property-trunc-Prop
        ( weak-modal-logic-closure axioms (a →ₘ b))
        ( forward-deduction-lemma a)
    pr2 (deduction-lemma a b) =
      map-universal-property-trunc-Prop
        ( weak-modal-logic-closure (theory-add-formula a axioms) b)
        ( is-in-weak-modal-logic-closure-weak-deduction ∘
          backward-deduction-lemma)
```

### TODO: List of assumptions

```agda
module _
  {l1 : Level} {i : Set l1}
  where

  list-assumptions-weak-deduction :
    {l2 : Level} {theory : modal-theory l2 i} {a : formula i} →
    theory ⊢w a → list (formula i)
  list-assumptions-weak-deduction =
    rec-weak-deduction
      ( λ {a} _ → cons a nil)
      ( λ _ _ l1 l2 → concat-list l1 l2)

  subset-theory-list-assumptions-weak-deduction :
    {l2 : Level} {theory : modal-theory l2 i} {a : formula i} →
    (d : theory ⊢w a) →
    list-subtype (list-assumptions-weak-deduction d) ⊆ theory
  subset-theory-list-assumptions-weak-deduction {theory = theory} =
    ind-weak-deduction
      ( λ d → list-subtype (list-assumptions-weak-deduction d) ⊆ theory)
      ( λ {a} in-axioms →
        ( subset-list-subtype-cons theory in-axioms
          ( subset-list-subtype-nil theory)))
      ( λ dab da sub1 sub2 →
        ( transitive-leq-subtype
          ( list-subtype
            ( concat-list
              ( list-assumptions-weak-deduction dab)
              ( list-assumptions-weak-deduction da)))
          ( list-subtype (list-assumptions-weak-deduction dab) ∪
              list-subtype (list-assumptions-weak-deduction da))
          ( theory)
          ( subtype-union-both
            ( list-subtype (list-assumptions-weak-deduction dab))
            ( list-subtype (list-assumptions-weak-deduction da))
            ( theory)
            ( sub1)
            ( sub2))
          ( subset-list-subtype-concat-union)))

  is-assumptions-list-assumptions-weak-deduction :
    {l2 : Level} {theory : modal-theory l2 i} {a : formula i} →
    (d : theory ⊢w a) →
    list-subtype (list-assumptions-weak-deduction d) ⊢w a
  is-assumptions-list-assumptions-weak-deduction {theory = theory} =
    ind-weak-deduction
      ( λ {a} d → list-subtype (list-assumptions-weak-deduction d) ⊢w a)
      ( λ _ → weak-deduction-ax head-in-list-subtype)
      ( λ dab da rab ra →
        ( weak-deduction-monotic
          {ax₁ = list-subtype (list-assumptions-weak-deduction dab) ∪
            list-subtype (list-assumptions-weak-deduction da)}
          ( subset-list-subtype-union-concat)
          ( weak-deduction-mp
            ( weak-deduction-monotic
              ( subtype-union-left
                ( list-subtype (list-assumptions-weak-deduction dab))
                ( list-subtype (list-assumptions-weak-deduction da)))
              ( rab))
            ( weak-deduction-monotic
              ( subtype-union-right
                ( list-subtype (list-assumptions-weak-deduction dab))
                ( list-subtype (list-assumptions-weak-deduction da)))
              ( ra)))))

module _
  {l1 l2 : Level} {i : Set l1} (axioms : modal-theory l2 i)
  (contains-ax-k : ax-k i ⊆ axioms)
  (contains-ax-s : ax-s i ⊆ axioms)
  (contains-ax-dn : ax-dn i ⊆ axioms)
  where

  -- TODO: move to formulas-deduction

  deduction-ex-falso :
    (a b : formula i) →
    is-in-subtype (weak-modal-logic-closure axioms) (~ a →ₘ a →ₘ b)
  deduction-ex-falso a b =
    forward-implication
      ( deduction-lemma axioms contains-ax-k contains-ax-s (~ a) (a →ₘ b))
      ( forward-implication
        ( deduction-lemma
          ( theory-add-formula (~ a) axioms)
          ( contains-ax-k')
          ( contains-ax-s')
          ( a)
          ( b))
        ( weak-modal-logic-closure-mp {a = ~~ b}
          ( weak-modal-logic-closure-ax
            ( contains-ax-dn'' (~~ b →ₘ b) (b , refl)))
          ( weak-modal-logic-closure-mp {a = ⊥}
            ( weak-modal-logic-closure-ax
              ( contains-ax-k'' (⊥ →ₘ ~ b →ₘ ⊥) (⊥ , ~ b , refl)))
            ( weak-modal-logic-closure-mp {a = a}
              ( weak-modal-logic-closure-ax
                ( subset-add-formula a
                  ( theory-add-formula (~ a) axioms)
                  ( ~ a)
                  ( formula-in-add-formula (~ a) axioms)))
              ( weak-modal-logic-closure-ax
                ( formula-in-add-formula a
                  ( theory-add-formula (~ a) axioms)))))))
    where
    contains-ax-k' : ax-k i ⊆ theory-add-formula (~ a) axioms
    contains-ax-k' =
      transitive-subset-add-formula (~ a) axioms (ax-k i) contains-ax-k

    contains-ax-s' : ax-s i ⊆ theory-add-formula (~ a) axioms
    contains-ax-s' =
      transitive-subset-add-formula (~ a) axioms (ax-s i) contains-ax-s

    contains-ax-k'' :
      ax-k i ⊆ theory-add-formula a (theory-add-formula (~ a) axioms)
    contains-ax-k'' =
      transitive-subset-add-formula a (theory-add-formula (~ a) axioms)
        ( ax-k i)
        ( contains-ax-k')

    contains-ax-dn'' :
      ax-dn i ⊆ theory-add-formula a (theory-add-formula (~ a) axioms)
    contains-ax-dn'' =
      transitive-subset-add-formula a
        ( theory-add-formula (~ a) axioms)
        ( ax-dn i)
        ( transitive-subset-add-formula (~ a) axioms (ax-dn i) contains-ax-dn)

  logic-ex-falso :
    (a b : formula i) →
    is-in-subtype (weak-modal-logic-closure axioms) a →
    is-in-subtype (weak-modal-logic-closure axioms) (~ a) →
    is-in-subtype (weak-modal-logic-closure axioms) b
  logic-ex-falso a b a-in-logic not-a-in-logic =
    weak-modal-logic-closure-mp
      ( weak-modal-logic-closure-mp
        ( deduction-ex-falso a b)
        ( not-a-in-logic))
      ( a-in-logic)
module _
  {l1 l2 : Level} {i : Set l1} (axioms : modal-theory l2 i)
  (contains-ax-k : ax-k i ⊆ axioms)
  (contains-ax-s : ax-s i ⊆ axioms)
  (contains-ax-dn : ax-dn i ⊆ axioms)
  where

  inv-deduction-ex-falso :
    (a b : formula i) →
    is-in-subtype (weak-modal-logic-closure axioms) (a →ₘ ~ a →ₘ b)
  inv-deduction-ex-falso a b =
    forward-implication
      ( deduction-lemma axioms contains-ax-k contains-ax-s a (~ a →ₘ b))
      ( forward-implication
        ( deduction-lemma
          ( theory-add-formula a axioms)
          ( contains-ax-k')
          ( contains-ax-s')
          ( ~ a)
          ( b))
        ( logic-ex-falso
          ( theory-add-formula (a →ₘ ⊥) (theory-add-formula a axioms))
          ( contains-ax-k'')
          ( contains-ax-s'')
          ( contains-ax-dn'')
          ( a)
          ( b)
          ( weak-modal-logic-closure-ax
            ( subset-add-formula (~ a) (theory-add-formula a axioms) a
              ( formula-in-add-formula a axioms)))
          ( weak-modal-logic-closure-ax
            ( formula-in-add-formula (~ a) (theory-add-formula a axioms)))))
    where
    contains-ax-k' : ax-k i ⊆ theory-add-formula a axioms
    contains-ax-k' =
      transitive-subset-add-formula a axioms (ax-k i) contains-ax-k

    contains-ax-s' : ax-s i ⊆ theory-add-formula a axioms
    contains-ax-s' =
      transitive-subset-add-formula a axioms (ax-s i) contains-ax-s

    contains-ax-k'' :
      ax-k i ⊆ theory-add-formula (~ a) (theory-add-formula a axioms)
    contains-ax-k'' =
      transitive-subset-add-formula (~ a) (theory-add-formula a axioms)
        ( ax-k i)
        ( contains-ax-k')

    contains-ax-s'' :
      ax-s i ⊆ theory-add-formula (~ a) (theory-add-formula a axioms)
    contains-ax-s'' =
      transitive-subset-add-formula (~ a) (theory-add-formula a axioms)
        ( ax-s i)
        ( contains-ax-s')

    contains-ax-dn'' :
      ax-dn i ⊆ theory-add-formula (~ a) (theory-add-formula a axioms)
    contains-ax-dn'' =
      transitive-subset-add-formula (~ a)
        ( theory-add-formula a axioms)
        ( ax-dn i)
        ( transitive-subset-add-formula a axioms (ax-dn i) contains-ax-dn)
```
