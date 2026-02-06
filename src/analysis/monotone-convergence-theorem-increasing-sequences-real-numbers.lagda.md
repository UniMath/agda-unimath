# Monotone convergence theorem for increasing sequences of real numbers

```agda
module analysis.monotone-convergence-theorem-increasing-sequences-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.axiom-of-countable-choice
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.universe-levels

open import lists.sequences

open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.increasing-sequences-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.limits-of-sequences-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.modulated-suprema-families-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.suprema-families-real-numbers
```

</details>

## Idea

The
{{#concept "monotone convergence theorem" WDID=Q4454933 WD="Weierstrass theorem" Disambiguation="increasing sequence of real numbers" Agda=is-limit-is-modulated-supremum-is-increasing-sequence-ℝ Agda=is-limit-is-supremum-is-increasing-sequence-ACℕ-ℝ}},
also known as **Weierstrass' theorem**, states that an
[increasing sequence](real-numbers.increasing-sequences-real-numbers.md) of
[real numbers](real-numbers.dedekind-real-numbers.md) with a
[modulated supremum](real-numbers.modulated-suprema-families-real-numbers.md)
converges to that supremum as a
[limit of sequences](real-numbers.limits-of-sequences-real-numbers.md). Because
modulated suprema are assumed to have supremum moduli, we can still obtain a
[convergence modulus](metric-spaces.limits-of-sequences-metric-spaces.md)
constructively. Assuming
[countable choice](foundation.axiom-of-countable-choice.md), ordinary suprema
are also modulated, yielding the monotone convergence theorem for ordinary
suprema.

## Construction

```agda
module _
  {l : Level}
  (u : sequence (ℝ l))
  (inc-u : is-increasing-sequence-ℝ u)
  (uω : ℝ l)
  (is-sup-uω : is-supremum-family-ℝ u uω)
  where

  left-leq-neighborhood-le-diff-error-is-supremum-is-increasing-sequence-ℝ :
    (ε : ℚ⁺) (n : ℕ) → leq-ℝ (u n) (uω +ℝ real-ℚ⁺ ε)
  left-leq-neighborhood-le-diff-error-is-supremum-is-increasing-sequence-ℝ ε n =
    transitive-leq-ℝ
      ( u n)
      ( uω)
      ( uω +ℝ real-ℚ⁺ ε)
      ( leq-left-add-real-ℚ⁺ uω ε)
      ( is-upper-bound-is-supremum-family-ℝ u uω is-sup-uω n)

  right-leq-neighborhood-le-diff-error-is-supremum-is-increasing-sequence-ℝ :
    (ε : ℚ⁺) (n m : ℕ) → leq-ℕ m n →
    le-ℝ (uω -ℝ real-ℚ⁺ ε) (u m) →
    leq-ℝ uω (u n +ℝ real-ℚ⁺ ε)
  right-leq-neighborhood-le-diff-error-is-supremum-is-increasing-sequence-ℝ
    ε n m m≤n uω-ε<u-m =
    transitive-leq-ℝ
      ( uω)
      ( u m +ℝ real-ℚ⁺ ε)
      ( u n +ℝ real-ℚ⁺ ε)
      ( preserves-leq-right-add-ℝ (real-ℚ⁺ ε) (u m) (u n) (inc-u m n m≤n))
      ( leq-le-ℝ
        ( le-transpose-left-diff-ℝ
          ( uω)
          ( real-ℚ⁺ ε)
          ( u m)
          ( uω-ε<u-m)))

  neighborhood-le-diff-error-is-supremum-is-increasing-sequence-ℝ :
    (ε : ℚ⁺) (n m : ℕ) → leq-ℕ m n →
    le-ℝ (uω -ℝ real-ℚ⁺ ε) (u m) →
    neighborhood-ℝ l ε (u n) uω
  neighborhood-le-diff-error-is-supremum-is-increasing-sequence-ℝ
    ε n m m≤n uω-ε<u-m =
    neighborhood-real-bound-each-leq-ℝ
      ( ε)
      ( u n)
      ( uω)
      ( left-leq-neighborhood-le-diff-error-is-supremum-is-increasing-sequence-ℝ
        ( ε)
        ( n))
      ( right-leq-neighborhood-le-diff-error-is-supremum-is-increasing-sequence-ℝ
        ( ε)
        ( n)
        ( m)
        ( m≤n)
        ( uω-ε<u-m))
```

## Theorem

### Monotone convergence theorem for modulated suprema

```agda
module _
  {l : Level}
  (u : sequence (ℝ l))
  (inc-u : is-increasing-sequence-ℝ u)
  where

  abstract
    is-limit-is-modulated-supremum-is-increasing-sequence-ℝ :
      (uω : ℝ l) →
      is-modulated-supremum-family-ℝ u uω →
      is-limit-sequence-ℝ u uω
    is-limit-is-modulated-supremum-is-increasing-sequence-ℝ
      uω (is-upper-bound-uω , is-modulus-uω) =
      map-trunc-Prop
        ( λ (μ : (ε : ℚ⁺) → Σ ℕ (λ i → le-ℝ (uω -ℝ real-ℚ⁺ ε) (u i))) →
          ( pr1 ∘ μ ,
            λ ε n mε≤n →
            neighborhood-le-diff-error-is-supremum-is-increasing-sequence-ℝ
              ( u)
              ( inc-u)
              ( uω)
              ( is-supremum-supremum-modulus-family-ℝ
                ( u)
                ( uω)
                ( is-upper-bound-uω , μ))
              ( ε)
              ( n)
              ( pr1 (μ ε))
              ( mε≤n)
              ( pr2 (μ ε))))
        ( is-modulus-uω)
```

### Monotone convergence theorem for suprema using countable choice

```agda
module _
  {l : Level}
  (acω : level-ACℕ l)
  (u : sequence (ℝ l))
  (inc-u : is-increasing-sequence-ℝ u)
  where

  is-limit-is-supremum-is-increasing-sequence-ACℕ-ℝ :
    (uω : ℝ l) →
    is-supremum-family-ℝ u uω →
    is-limit-sequence-ℝ u uω
  is-limit-is-supremum-is-increasing-sequence-ACℕ-ℝ uω H =
    is-limit-is-modulated-supremum-is-increasing-sequence-ℝ u
      ( inc-u)
      ( uω)
      ( is-modulated-supremum-is-supremum-family-ACℕ-ℝ acω ℕ-Set u uω H)
```

## External links

- [Monotone convergence theorem](https://en.wikipedia.org/wiki/Monotone_convergence_theorem)
  on Wikipedia
