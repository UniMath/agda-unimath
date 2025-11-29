# Monotonic functions on the real numbers

```agda
module real-numbers.monotonic-functions-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import order-theory.posets
open import order-theory.order-preserving-maps-posets
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import elementary-number-theory.addition-positive-rational-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import foundation.coproduct-types
open import foundation.empty-types
open import foundation.propositional-truncations
open import real-numbers.similarity-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.inequality-real-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import real-numbers.strict-inequality-real-numbers
open import foundation.propositions
open import foundation.double-negation
open import real-numbers.dedekind-real-numbers
open import foundation.universe-levels
```

</details>

## Idea

## Definition

```agda
is-monotonic-prop-function-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → Prop (lsuc l1 ⊔ l2)
is-monotonic-prop-function-ℝ {l1} {l2} =
  preserves-order-prop-Poset (ℝ-Poset l1) (ℝ-Poset l2)

is-monotonic-function-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → UU (lsuc l1 ⊔ l2)
is-monotonic-function-ℝ f = type-Prop (is-monotonic-prop-function-ℝ f)
```

## Properties

### If `x < y` implies `f x ≤ f y`, then `x ≤ y` implies `f x ≤ f y`

```agda
module _
  {l1 l2 : Level}
  (f : ℝ l1 → ℝ l2)
  (H : ((x y : ℝ l1) → le-ℝ x y → leq-ℝ (f x) (f y)))
  where

  abstract
    strengthen-is-monotonic-function-ℝ : is-monotonic-function-ℝ f
    strengthen-is-monotonic-function-ℝ x y x≤y =
      double-negation-elim-leq-ℝ
        ( f x)
        ( f y)
        ( map-double-negation
          ( rec-coproduct
            ( λ x~y → leq-eq-ℝ (ap f (eq-sim-ℝ x~y)))
            ( H x y))
          ( irrefutable-sim-or-le-leq-ℝ x y x≤y))
```

### If `f` is continuous and monotonic on the rational real numbers, it is monotonic on the real numbers

```agda
module _
  {l1 l2 : Level}
  (f : ℝ l1 → ℝ l2)
  (H :
    ( (p q : ℚ) → leq-ℚ p q →
      leq-ℝ (f (raise-real-ℚ l1 p)) (f (raise-real-ℚ l1 q))))
  where

  abstract
    is-monotonic-is-monotonic-on-rational-ℝ : is-monotonic-function-ℝ f
    is-monotonic-is-monotonic-on-rational-ℝ =
      let
        open do-syntax-trunc-Prop empty-Prop
      in
        strengthen-is-monotonic-function-ℝ
          ( f)
          ( λ x y x<y →
            leq-not-le-ℝ
              ( f y)
              ( f x)
              ( λ fy<fx →
                do
                  (ε , fy+ε<fx) ← exists-positive-rational-separation-le-ℝ fy<fx
                  let (ε₁ , ε₂ , ε₁+ε₂) = split-ℚ⁺ ε
                  {!   !}))
```
