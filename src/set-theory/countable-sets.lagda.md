# Countable sets

```agda
module set-theory.countable-sets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.complements-subtypes
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.functions
open import foundation.functoriality-coproduct-types
open import foundation.maybe
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.surjective-maps
open import foundation.type-arithmetic-coproduct-types
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A set `X` is said to be countable if there is a surjective map `f : ℕ → X + 1`. Equivalently, a set `X` is countable if there is a surjective map `f : type-decidable-subset P → X` for some decidable subset `P` of `X`.

## Definition

### First definition of countable types

```agda
is-countable-Prop : {l : Level} → Set l → Prop l
is-countable-Prop X = ∃-Prop (ℕ → Maybe (type-Set X)) is-surjective

is-countable : {l : Level} → Set l → UU l
is-countable X = type-Prop (is-countable-Prop X)

is-prop-is-countable : {l : Level} (X : Set l) → is-prop (is-countable X)
is-prop-is-countable X = is-prop-type-Prop (is-countable-Prop X)
```

### Second definition of countable types

```agda
is-countable-Prop' : {l : Level} → Set l → Prop (lsuc lzero ⊔ l)
is-countable-Prop' X =
  ∃-Prop
    ( decidable-subtype lzero ℕ)
    ( λ P → type-decidable-subtype P ↠ type-Set X)

is-countable' : {l : Level} → Set l → UU (lsuc lzero ⊔ l)
is-countable' X = type-Prop (is-countable-Prop' X)

is-prop-is-countable' : {l : Level} (X : Set l) → is-prop (is-countable' X)
is-prop-is-countable' X = is-prop-type-Prop (is-countable-Prop' X)
```

## Properties

### The two definitions of countability are equivalent

```agda
module _
  {l : Level} (X : Set l)
  where

{-
  is-countable-is-countable' :
    is-countable' X → is-countable X
  is-countable-is-countable' H =
    apply-universal-property-trunc-Prop H
      ( is-countable-Prop X)
      ( λ (P , f) →
        unit-trunc-Prop
          ( pair
            ( λ n →
              map-coprod
                ( λ { (zero-ℕ , p) → ex-falso p ;
                      (succ-ℕ n , p) → map-surjection f (n , p)})
                ( λ x → star)
                ( map-left-distributive-Σ-coprod ℕ
                  ( {!is-in-decidable-subtype ∘ ?!})
                  ( ¬ ∘ shift-ℕ empty (is-in-decidable-subtype P))
                  ( pair n
                    ( is-decidable-subtype-decidable-subtype
                      ( shift-ℕ empty-decidable-Prop P) {!!}))))
            {!!}))
            -}
```

-- ℕ → Σ (n : ℕ), P' n + ¬ (P' n)
--   → (Σ (n : ℕ), P' n) + (Σ (n : ℕ), ¬ (P' n))
--   → X + 1

-- P' := shift-ℕ ∅ P
