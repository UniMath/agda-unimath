# Uncountability of the MacNeille real numbers

```agda
module real-numbers.uncountability-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.law-of-excluded-middle
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.surjective-maps
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.located-macneille-real-numbers
open import real-numbers.macneille-real-numbers
open import real-numbers.predicative-levy-uncountability-argument-macneille-real-numbers
open import real-numbers.rational-macneille-real-numbers
open import real-numbers.zero-macneille-real-numbers

open import set-theory.countable-sets
open import set-theory.sequence-avoiding-sets
open import set-theory.uncountable-sets
```

</details>

## Idea

The [MacNeille reals](real-numbers.macneille-real-numbers.md) form an
[uncountable set](set-theory.uncountable-sets.md). In fact, they form a
[sequence-avoiding set](set-theory.sequence-avoiding-sets.md).

## Theorem

For every sequence `f : ℕ → ℝₘ` we may construct a MacNeille real not in the
image of `f`.

```agda
not-in-sequence-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) →
  Σ (macneille-ℝ l) (λ x0 → (n : ℕ) → f n ≠ x0)
not-in-sequence-macneille-ℝ f =
  sequence-avoiding-point-levy-macneille-ℝ f
```

## Corollaries

### The MacNeille real numbers are sequence-avoiding

```agda
abstract
  is-sequence-avoiding-macneille-ℝ :
    {l : Level} → is-sequence-avoiding (set-macneille-ℝ l)
  is-sequence-avoiding-macneille-ℝ f =
    let (x0 , H) = not-in-sequence-macneille-ℝ f in
    unit-trunc-Prop (x0 , λ n p → H n (inv p))
```

### No map `ℕ → ℝₘ` is surjective

```agda
abstract
  is-not-surjective-sequence-macneille-ℝ :
    {l : Level} (f : ℕ → macneille-ℝ l) → ¬ is-surjective f
  is-not-surjective-sequence-macneille-ℝ {l} f H =
    is-not-directly-countable-is-sequence-avoiding
      ( set-macneille-ℝ l)
      ( is-sequence-avoiding-macneille-ℝ)
      ( unit-trunc-Prop (f , H))
```

### The MacNeille real numbers are uncountable

```agda
abstract
  is-uncountable-macneille-ℝ :
    {l : Level} → is-uncountable (set-macneille-ℝ l)
  is-uncountable-macneille-ℝ {l} =
    is-uncountable-is-sequence-avoiding
      ( set-macneille-ℝ l)
      ( raise-zero-macneille-ℝ l)
      ( is-sequence-avoiding-macneille-ℝ)
```

### Under excluded middle, the Dedekind reals are uncountable

```agda
abstract
  is-uncountable-ℝ-LEM :
    {l : Level} (lem : level-LEM l) → is-uncountable (ℝ-Set l)
  is-uncountable-ℝ-LEM {l} lem C =
    is-uncountable-macneille-ℝ
      ( is-countable-equiv
        ( ℝ-Set l)
        ( set-macneille-ℝ l)
        ( equiv-macneille-ℝ-LEM lem)
        ( C))
```
