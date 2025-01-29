# Signs of real numbers

```agda
module real-numbers.negation-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

The negation of a Dedekind real number with cuts `L, U` has lower cut equal to
the negation of elements of `U`, and upper cut equal to the negation of elements
in `L`.

```agda
module _
  {l : Level} (x : ℝ l)
  where

  lower-cut-neg-ℝ : subtype l ℚ
  lower-cut-neg-ℝ q = upper-cut-ℝ x (neg-ℚ q)

  upper-cut-neg-ℝ : subtype l ℚ
  upper-cut-neg-ℝ q = lower-cut-ℝ x (neg-ℚ q)

  is-inhabited-lower-cut-neg-ℝ : exists ℚ lower-cut-neg-ℝ
  inhabited-lower-cut-neg-ℝ =
    elim-exists
      (∃ ℚ lower-cut-neg-ℝ)
      (λ q q-in-upper →
        intro-exists
          (neg-ℚ q)
          (tr (is-in-upper-cut-ℝ x) (inv (neg-neg-ℚ q)) q-in-upper))
      (is-inhabited-upper-cut-ℝ x)

  is-inhabited-upper-cut-neg-ℝ : exists ℚ upper-cut-neg-ℝ
  is-inhabited-upper-cut-neg-ℝ =
    elim-exists
      (∃ ℚ upper-cut-neg-ℝ)
      (λ q q-in-lower →
        intro-exists
          (neg-ℚ q)
          (tr (is-in-lower-cut-ℝ x) (inv (neg-neg-ℚ q)) q-in-lower))
      (is-inhabited-lower-cut-ℝ x)

  is-rounded-lower-cut-neg-ℝ :
    (q : ℚ) →
    is-in-subtype lower-cut-neg-ℝ q ↔
    exists ℚ (λ r → (le-ℚ-Prop q r) ∧ (lower-cut-neg-ℝ r))
  pr1 (is-rounded-lower-cut-neg-ℝ q) in-neg-lower =
    elim-exists
      (∃ ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-neg-ℝ r))
      (λ r (r<-q , in-upper-r) →
        intro-exists
          (neg-ℚ r)
          (tr
            (λ x → le-ℚ x (neg-ℚ r))
            (neg-neg-ℚ q)
            (neg-le-ℚ r (neg-ℚ q) r<-q) ,
           tr (is-in-upper-cut-ℝ x) (inv (neg-neg-ℚ r)) in-upper-r))
      (forward-implication (is-rounded-upper-cut-ℝ x (neg-ℚ q)) in-neg-lower)
  pr2 (is-rounded-lower-cut-neg-ℝ q) exists-r =
    backward-implication
      (is-rounded-upper-cut-ℝ x (neg-ℚ q))
      (elim-exists
        (∃ ℚ (λ r → le-ℚ-Prop r (neg-ℚ q) ∧ upper-cut-ℝ x r))
        (λ r (q<r , in-neg-lower-r) →
          intro-exists (neg-ℚ r) (neg-le-ℚ q r q<r , in-neg-lower-r))
        exists-r)

  is-rounded-upper-cut-neg-ℝ :
    (r : ℚ) →
    is-in-subtype upper-cut-neg-ℝ r ↔
    exists ℚ (λ q → (le-ℚ-Prop q r) ∧ (upper-cut-neg-ℝ q))
  pr1 (is-rounded-upper-cut-neg-ℝ r) in-neg-upper =
    elim-exists
      (∃ ℚ (λ q → le-ℚ-Prop q r ∧ upper-cut-neg-ℝ q))
      (λ q (-r<q , in-lower-q) →
        intro-exists
          (neg-ℚ q)
          (tr (le-ℚ (neg-ℚ q)) (neg-neg-ℚ r) (neg-le-ℚ (neg-ℚ r) q -r<q) ,
            tr (is-in-lower-cut-ℝ x) (inv (neg-neg-ℚ q)) in-lower-q))
      (forward-implication (is-rounded-lower-cut-ℝ x (neg-ℚ r)) in-neg-upper)
  pr2 (is-rounded-upper-cut-neg-ℝ r) exists-q =
    backward-implication
      (is-rounded-lower-cut-ℝ x (neg-ℚ r))
      (elim-exists
        (∃ ℚ (λ q → le-ℚ-Prop (neg-ℚ r) q ∧ lower-cut-ℝ x q))
        (λ q (q<r , in-neg-upper-q) →
          intro-exists (neg-ℚ q) (neg-le-ℚ q r q<r , in-neg-upper-q))
        exists-q)

  is-disjoint-cut-neg-ℝ :
    (q : ℚ) →
      ¬ (is-in-subtype lower-cut-neg-ℝ q × is-in-subtype upper-cut-neg-ℝ q)
  is-disjoint-cut-neg-ℝ q (in-lower-neg , in-upper-neg) =
    is-disjoint-cut-ℝ x (neg-ℚ q) (in-upper-neg , in-lower-neg)

  is-located-lower-upper-cut-neg-ℝ :
    (q r : ℚ) → le-ℚ q r →
      type-disjunction-Prop (lower-cut-neg-ℝ q) (upper-cut-neg-ℝ r)
  is-located-lower-upper-cut-neg-ℝ q r q<r =
    elim-disjunction
      (disjunction-Prop (lower-cut-neg-ℝ q) (upper-cut-neg-ℝ r))
      inr-disjunction
      inl-disjunction
      (is-located-lower-upper-cut-ℝ x (neg-ℚ r) (neg-ℚ q) (neg-le-ℚ q r q<r))

  neg-ℝ : ℝ l
  neg-ℝ =
    real-dedekind-cut
      lower-cut-neg-ℝ
      upper-cut-neg-ℝ
      ((is-inhabited-lower-cut-neg-ℝ , is-inhabited-upper-cut-neg-ℝ) ,
        (is-rounded-lower-cut-neg-ℝ , is-rounded-upper-cut-neg-ℝ) ,
          is-disjoint-cut-neg-ℝ , is-located-lower-upper-cut-neg-ℝ)

neg-neg-ℝ : {l : Level} → (x : ℝ l) → neg-ℝ (neg-ℝ x) ＝ x
neg-neg-ℝ x =
  eq-eq-lower-cut-ℝ
    (neg-ℝ (neg-ℝ x))
    x
    (eq-has-same-elements-subtype
      (lower-cut-ℝ (neg-ℝ (neg-ℝ x)))
      (lower-cut-ℝ x)
      (λ q →
        tr (is-in-lower-cut-ℝ x) (neg-neg-ℚ q) ,
        tr (is-in-lower-cut-ℝ x) (inv (neg-neg-ℚ q))))
```
