# Repetitions in sequences

```agda
module lists.repetitions-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strictly-ordered-pairs-of-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.negated-equality
open import foundation.pairs-of-distinct-elements
open import foundation.repetitions-of-values
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.injective-maps

open import lists.sequences
```

</details>

## Idea

A repetition in a sequence `a : ℕ → A` consists of a pair of distinct natural
numbers `m` and `n` such that `a m = a n`.

## Definition

### Repetitions of values in a sequence

```agda
is-repetition-of-values-sequence :
  {l : Level} {A : UU l} (a : sequence A) (p : pair-of-distinct-elements ℕ) →
  UU l
is-repetition-of-values-sequence a p =
  is-repetition-of-values a p

repetition-of-values-sequence :
  {l : Level} {A : UU l} → sequence A → UU l
repetition-of-values-sequence a =
  Σ (pair-of-distinct-elements ℕ) (is-repetition-of-values a)

module _
  {l : Level} {A : UU l} (a : sequence A) (r : repetition-of-values-sequence a)
  where

  pair-of-distinct-elements-repetition-of-values-sequence :
    pair-of-distinct-elements ℕ
  pair-of-distinct-elements-repetition-of-values-sequence = pr1 r

  first-repetition-of-values-sequence : ℕ
  first-repetition-of-values-sequence =
    first-pair-of-distinct-elements
      pair-of-distinct-elements-repetition-of-values-sequence

  second-repetition-of-values-sequence : ℕ
  second-repetition-of-values-sequence =
    second-pair-of-distinct-elements
      pair-of-distinct-elements-repetition-of-values-sequence

  distinction-repetition-of-values-sequence :
    first-repetition-of-values-sequence ≠ second-repetition-of-values-sequence
  distinction-repetition-of-values-sequence =
    distinction-pair-of-distinct-elements
      pair-of-distinct-elements-repetition-of-values-sequence

  is-repetition-of-values-repetition-of-values-sequence :
    is-repetition-of-values a
      pair-of-distinct-elements-repetition-of-values-sequence
  is-repetition-of-values-repetition-of-values-sequence = pr2 r
```

### Ordered repetitions of values in a sequence

```agda
is-ordered-repetition-of-values-ℕ :
  {l1 : Level} {A : UU l1} (f : ℕ → A) (x : strictly-ordered-pair-ℕ) → UU l1
is-ordered-repetition-of-values-ℕ f x =
  f (first-strictly-ordered-pair-ℕ x) ＝ f (second-strictly-ordered-pair-ℕ x)

ordered-repetition-of-values-ℕ :
  {l1 : Level} {A : UU l1} (f : ℕ → A) → UU l1
ordered-repetition-of-values-ℕ f =
  Σ strictly-ordered-pair-ℕ (is-ordered-repetition-of-values-ℕ f)

ordered-repetition-of-values-comp-ℕ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (g : A → B) {f : ℕ → A} →
  ordered-repetition-of-values-ℕ f →
  ordered-repetition-of-values-ℕ (g ∘ f)
ordered-repetition-of-values-comp-ℕ g ((a , b , H) , p) =
  ((a , b , H) , ap g p)

ordered-repetition-of-values-right-factor-ℕ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {g : A → B} {f : ℕ → A} →
  is-emb g → ordered-repetition-of-values-ℕ (g ∘ f) →
  ordered-repetition-of-values-ℕ f
ordered-repetition-of-values-right-factor-ℕ E ((a , b , H) , p) =
  ((a , b , H) , is-injective-is-emb E p)
```

### Any repetition of values in a sequence can be ordered

```agda
module _
  {l : Level} {A : UU l}
  where

  ordered-repetition-of-values-repetition-of-values-ℕ' :
    (f : ℕ → A) (a b : ℕ) → a ≠ b → f a ＝ f b →
    ordered-repetition-of-values-ℕ f
  ordered-repetition-of-values-repetition-of-values-ℕ' f zero-ℕ zero-ℕ H p =
    ex-falso (H refl)
  ordered-repetition-of-values-repetition-of-values-ℕ' f zero-ℕ (succ-ℕ b) H p =
    ((0 , succ-ℕ b , star) , p)
  ordered-repetition-of-values-repetition-of-values-ℕ' f (succ-ℕ a) zero-ℕ H p =
    ((0 , succ-ℕ a , star) , inv p)
  ordered-repetition-of-values-repetition-of-values-ℕ' f
    (succ-ℕ a) (succ-ℕ b) H p =
    map-Σ
      ( λ u → f (pr1 u) ＝ f (pr1 (pr2 u)))
      ( map-Σ _ succ-ℕ (λ _ → map-Σ _ succ-ℕ (λ _ → id)))
      ( λ u → id)
      ( ordered-repetition-of-values-repetition-of-values-ℕ'
        ( f ∘ succ-ℕ)
        ( a)
        ( b)
        ( λ q → H (ap succ-ℕ q))
        ( p))

  ordered-repetition-of-values-repetition-of-values-ℕ :
    (f : ℕ → A) → repetition-of-values f → ordered-repetition-of-values-ℕ f
  ordered-repetition-of-values-repetition-of-values-ℕ f ((a , b , H) , p) =
    ordered-repetition-of-values-repetition-of-values-ℕ' f a b H p
```
