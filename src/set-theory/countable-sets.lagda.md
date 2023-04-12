# Countable sets

```agda
module set-theory.countable-sets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.decidable-subtypes
open import foundation.existential-quantification
open import foundation.maybe
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.shifting-sequences
open import foundation.surjective-maps
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.dependent-pair-types
open import foundation-core.fibers-of-maps
open import foundation-core.functions
open import foundation-core.identity-types
```

</details>

## Idea

A set `X` is said to be countable if there is a surjective map `f : ℕ → X + 1`.
Equivalently, a set `X` is countable if there is a surjective map
`f : type-decidable-subset P → X` for some decidable subset `P` of `X`.

## Definition

### First definition of countable types

```agda
is-countable-Prop : {l : Level} → Set l → Prop l
is-countable-Prop X = ∃-Prop (ℕ → Maybe (type-Set X)) is-surjective

is-countable : {l : Level} → Set l → UU l
is-countable X = type-Prop (is-countable-Prop X)

is-prop-is-countable :
  {l : Level} (X : Set l) → is-prop (is-countable X)
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

is-prop-is-countable' :
  {l : Level} (X : Set l) → is-prop (is-countable' X)
is-prop-is-countable' X = is-prop-type-Prop (is-countable-Prop' X)
```

### Third definition of countable types

If a set `X` is inhabited, then it is countable if and only if there is a
surjective map `f : ℕ → X`. Let us call the latter as "directly countable".

```agda
is-directly-countable-Prop : {l : Level} → Set l → Prop l
is-directly-countable-Prop X =
  ∃-Prop (ℕ → type-Set X) is-surjective

is-directly-countable : {l : Level} → Set l → UU l
is-directly-countable X = type-Prop (is-directly-countable-Prop X)

is-prop-is-directly-countable :
  {l : Level} (X : Set l) → is-prop (is-directly-countable X)
is-prop-is-directly-countable X = is-prop-type-Prop
  (is-directly-countable-Prop X)

module _
  {l : Level} (X : Set l) (a : type-Set X)
  where

  is-directly-countable-is-countable :
    is-countable X → is-directly-countable X
  is-directly-countable-is-countable H =
    apply-universal-property-trunc-Prop H
      ( is-directly-countable-Prop X)
      ( λ P →
        unit-trunc-Prop
          ( pair
            ( f ∘ (pr1 P))
            ( is-surjective-comp is-surjective-f (pr2 P))))
    where
     f : Maybe (type-Set X) → type-Set X
     f (inl x) = x
     f (inr star) = a

     is-surjective-f : is-surjective f
     is-surjective-f x = unit-trunc-Prop (pair (inl x) refl)

  is-countable-is-directly-countable :
    is-directly-countable X → is-countable X
  is-countable-is-directly-countable H =
    apply-universal-property-trunc-Prop H
      ( is-countable-Prop X)
      ( λ P →
        unit-trunc-Prop
          ( pair
            ( λ {
              zero-ℕ → inr star ;
              (succ-ℕ n) → inl ((shift-ℕ a (pr1 P)) n)})
            ( λ {
              (inl x) →
                apply-universal-property-trunc-Prop (pr2 P x)
                  ( trunc-Prop (fib _ (inl x)))
                  ( λ { (pair n p) →
                    unit-trunc-Prop
                      ( pair (succ-ℕ (succ-ℕ n)) (ap inl p))}) ;
              (inr star) → unit-trunc-Prop (pair zero-ℕ refl)})))
```

## Properties

### The two definitions of countability are equivalent

## Examples

The set of natural numbers ℕ is itself countable.

```agda
is-countable-ℕ : is-countable ℕ-Set
is-countable-ℕ =
  unit-trunc-Prop
    ( pair
      ( λ { zero-ℕ → inr star ; (succ-ℕ n) → inl n})
      ( λ {
        (inl n) → unit-trunc-Prop (pair (succ-ℕ n) refl) ;
        (inr star) → unit-trunc-Prop (pair zero-ℕ refl)}))
```
