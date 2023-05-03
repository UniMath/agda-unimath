# Formalisation of the Symmetry Book - 24 pushouts

```agda
module synthetic-homotopy-theory.24-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Exercises

### Exercise 13.1

### Exercise 13.2

```agda
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
```

### Exercise 16.2

```agda
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
