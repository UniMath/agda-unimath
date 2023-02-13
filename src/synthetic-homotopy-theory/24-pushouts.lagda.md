{{#title  Formalisation of the Symmetry Book}}

```agda
module synthetic-homotopy-theory.24-pushouts where

open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.cones-pullbacks
open import foundation.constant-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.pullbacks
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.unit-type
open import foundation.universal-property-pullbacks
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-pushouts
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts

-- Exercises

-- Exercise 13.1

-- Exercise 13.2

is-equiv-cofiber-point :
  {l : Level} {B : UU l} (b : B) →
  is-equiv (pr1 (cocone-pushout (const unit B b) (const unit unit star)))
is-equiv-cofiber-point {l} {B} b =
  is-equiv-universal-property-pushout'
    ( const unit B b)
    ( const unit unit star)
    ( cocone-pushout (const unit B b) (const unit unit star))
    ( is-equiv-is-contr (const unit unit star) is-contr-unit is-contr-unit)
    ( up-pushout (const unit B b) (const unit unit star))

-- Exercise 16.2

-- ev-disjunction :
--   {l1 l2 l3 : Level} (P : Prop l1) (Q : Prop l2) (R : Prop l3) →
--   ((type-Prop P) * (type-Prop Q) → (type-Prop R)) →
--   (type-Prop P → type-Prop R) × (type-Prop Q → type-Prop R)
-- ev-disjunction P Q R f =
--   pair
--     ( f ∘ (inl-join (type-Prop P) (type-Prop Q)))
--     ( f ∘ (inr-join (type-Prop P) (type-Prop Q)))

-- comparison-ev-disjunction :
--   {l1 l2 l3 : Level} (P : Prop l1) (Q : Prop l2) (R : Prop l3) →
--   cocone-join (type-Prop P) (type-Prop Q) (type-Prop R)

-- universal-property-disjunction-join-prop :
--   {l1 l2 l3 : Level} (P : Prop l1) (Q : Prop l2) (R : Prop l3) →
--   is-equiv (ev-disjunction P Q R)
```
