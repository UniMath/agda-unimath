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
{{#concept "monotone convergence theorem" WDID=Q4454933 WD="Weierstrass theorem" Disambiguation="increasing sequence of real numbers" Agda=is-limit-is-modulated-supremum-is-increasing-sequence-ℝ Agda=is-limit-is-supremum-is-increasing-sequence-ACℕ-ℝ}}
states that an
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
  (v : ℝ l)
  (is-sup-v : is-supremum-family-ℝ u v)
  where

  abstract
    left-leq-neighborhood-le-diff-error-is-supremum-is-increasing-sequence-ℝ :
      (ε : ℚ⁺) (n : ℕ) → leq-ℝ (u n) (v +ℝ real-ℚ⁺ ε)
    left-leq-neighborhood-le-diff-error-is-supremum-is-increasing-sequence-ℝ
      ε n =
      transitive-leq-ℝ
        ( u n)
        ( v)
        ( v +ℝ real-ℚ⁺ ε)
        ( leq-left-add-real-ℚ⁺ v ε)
        ( is-upper-bound-is-supremum-family-ℝ u v is-sup-v n)

  abstract
    right-leq-neighborhood-le-diff-error-is-supremum-is-increasing-sequence-ℝ :
      (ε : ℚ⁺) (n m : ℕ) → leq-ℕ m n →
      le-ℝ (v -ℝ real-ℚ⁺ ε) (u m) →
      leq-ℝ v (u n +ℝ real-ℚ⁺ ε)
    right-leq-neighborhood-le-diff-error-is-supremum-is-increasing-sequence-ℝ
      ε n m m≤n v-ε<u-m =
      transitive-leq-ℝ
        ( v)
        ( u m +ℝ real-ℚ⁺ ε)
        ( u n +ℝ real-ℚ⁺ ε)
        ( preserves-leq-right-add-ℝ (real-ℚ⁺ ε) (u m) (u n) (inc-u m n m≤n))
        ( leq-le-ℝ
          ( le-transpose-left-diff-ℝ
            ( v)
            ( real-ℚ⁺ ε)
            ( u m)
            ( v-ε<u-m)))

  abstract
    neighborhood-le-diff-error-is-supremum-is-increasing-sequence-ℝ :
      (ε : ℚ⁺) (n m : ℕ) → leq-ℕ m n →
      le-ℝ (v -ℝ real-ℚ⁺ ε) (u m) →
      neighborhood-ℝ l ε (u n) v
    neighborhood-le-diff-error-is-supremum-is-increasing-sequence-ℝ
      ε n m m≤n v-ε<u-m =
      neighborhood-real-bound-each-leq-ℝ
        ( ε)
        ( u n)
        ( v)
        ( left-leq-neighborhood-le-diff-error-is-supremum-is-increasing-sequence-ℝ
          ( ε)
          ( n))
        ( right-leq-neighborhood-le-diff-error-is-supremum-is-increasing-sequence-ℝ
          ( ε)
          ( n)
          ( m)
          ( m≤n)
          ( v-ε<u-m))
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
      (v : ℝ l) →
      is-modulated-supremum-family-ℝ u v →
      is-limit-sequence-ℝ u v
    is-limit-is-modulated-supremum-is-increasing-sequence-ℝ
      v (is-upper-bound-v , is-modulus-v) =
      map-trunc-Prop
        ( λ (μ : (ε : ℚ⁺) → Σ ℕ (λ i → le-ℝ (v -ℝ real-ℚ⁺ ε) (u i))) →
          ( pr1 ∘ μ ,
            λ ε n mε≤n →
            neighborhood-le-diff-error-is-supremum-is-increasing-sequence-ℝ
              ( u)
              ( inc-u)
              ( v)
              ( is-supremum-supremum-modulus-family-ℝ
                ( u)
                ( v)
                ( is-upper-bound-v , μ))
              ( ε)
              ( n)
              ( pr1 (μ ε))
              ( mε≤n)
              ( pr2 (μ ε))))
        ( is-modulus-v)
```

### Monotone convergence theorem for suprema using countable choice

```agda
module _
  {l : Level}
  (acℕ : level-ACℕ l)
  (u : sequence (ℝ l))
  (inc-u : is-increasing-sequence-ℝ u)
  where

  abstract
    is-limit-is-supremum-is-increasing-sequence-ACℕ-ℝ :
      (v : ℝ l) →
      is-supremum-family-ℝ u v →
      is-limit-sequence-ℝ u v
    is-limit-is-supremum-is-increasing-sequence-ACℕ-ℝ v H =
      is-limit-is-modulated-supremum-is-increasing-sequence-ℝ u
        ( inc-u)
        ( v)
        ( is-modulated-supremum-is-supremum-family-ACℕ-ℝ acℕ ℕ-Set u v H)
```

## External links

- [Monotone convergence theorem](https://en.wikipedia.org/wiki/Monotone_convergence_theorem)
  on Wikipedia
