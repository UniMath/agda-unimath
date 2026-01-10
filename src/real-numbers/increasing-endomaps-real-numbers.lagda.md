# Increasing endomaps on the real numbers

```agda
module real-numbers.increasing-endomaps-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.order-preserving-maps-posets
open import order-theory.subposets

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.subsets-real-numbers
```

</details>

## Idea

A function `f` from the [real numbers](real-numbers.dedekind-real-numbers.md) to
themselves is
{{#concept "increasing" Disambiguation="function from ℝ to ℝ" Agda=is-increasing-endomap-ℝ}}
if for all `x ≤ y`, `f x ≤ f y`; in other words, it is an
[order-preserving map](order-theory.order-preserving-maps-posets.md) on the
[poset of real numbers](real-numbers.inequality-real-numbers.md).

Several arguments on this page are due to
[Mark Saving](https://math.stackexchange.com/users/798694/mark-saving) in this
Mathematics Stack Exchange answer: <https://math.stackexchange.com/q/5107860>.

## Definition

```agda
is-increasing-prop-endomap-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → Prop (lsuc l1 ⊔ l2)
is-increasing-prop-endomap-ℝ {l1} {l2} =
  preserves-order-prop-Poset (ℝ-Poset l1) (ℝ-Poset l2)

is-increasing-endomap-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → UU (lsuc l1 ⊔ l2)
is-increasing-endomap-ℝ f = type-Prop (is-increasing-prop-endomap-ℝ f)

is-increasing-on-subset-endomap-ℝ :
  {l1 l2 l3 : Level} (f : ℝ l1 → ℝ l2) (S : subset-ℝ l3 l1) →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
is-increasing-on-subset-endomap-ℝ f S =
  preserves-order-Poset
    ( poset-Subposet (ℝ-Poset _) S)
    ( ℝ-Poset _)
    ( f ∘ inclusion-subset-ℝ S)
```

## Properties

### If `x < y` implies `f x ≤ f y`, then `f` is increasing

```agda
module _
  {l1 l2 : Level}
  (f : ℝ l1 → ℝ l2)
  where

  abstract
    is-increasing-is-increasing-on-strict-inequalities-endomap-ℝ :
      ((x y : ℝ l1) → le-ℝ x y → leq-ℝ (f x) (f y)) →
      is-increasing-endomap-ℝ f
    is-increasing-is-increasing-on-strict-inequalities-endomap-ℝ H x y x≤y =
      double-negation-elim-leq-ℝ
        ( f x)
        ( f y)
        ( map-double-negation
          ( rec-coproduct
            ( λ x~y → leq-eq-ℝ (ap f (eq-sim-ℝ x~y)))
            ( H x y))
          ( irrefutable-sim-or-le-leq-ℝ x y x≤y))

module _
  {l1 l2 l3 : Level}
  (f : ℝ l1 → ℝ l2)
  (S : subset-ℝ l3 l1)
  where

  abstract
    is-increasing-is-increasing-on-strict-inequalities-on-subset-endomap-ℝ :
      ( ((x y : type-subset-ℝ S) →
        le-ℝ (pr1 x) (pr1 y) → leq-ℝ (f (pr1 x)) (f (pr1 y)))) →
      is-increasing-on-subset-endomap-ℝ f S
    is-increasing-is-increasing-on-strict-inequalities-on-subset-endomap-ℝ
      H (x , x∈S) (y , y∈S) x≤y =
      double-negation-elim-leq-ℝ
        ( f x)
        ( f y)
        ( map-double-negation
          ( rec-coproduct
            ( λ x~y → leq-eq-ℝ (ap f (eq-sim-ℝ x~y)))
            ( H (x , x∈S) (y , y∈S)))
          ( irrefutable-sim-or-le-leq-ℝ x y x≤y))
```
