# Eventually constant sequences

```agda
module foundation.eventually-constant-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.based-induction-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.eventually-equal-sequences
open import foundation.eventually-pointed-sequences-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.sequences
open import foundation.universe-levels
```

</details>

## Idea

A [sequence](foundation.sequences.md) `u` is
{{#concept "eventually constant" Disambiguation="sequence" Agda=is-eventually-constant-sequence}}
if `u p ＝ u q` for sufficiently large `p` and `q`.

## Definitions

### Eventually constant sequences

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  has-modulus-eventually-constant-sequence : UU l
  has-modulus-eventually-constant-sequence =
    has-modulus-eventually-pointed-sequence
      (λ p → has-modulus-eventually-pointed-sequence (λ q → u p ＝ u q))
```

### The eventual value of an eventually constant sequence

```agda
module _
  {l : Level} {A : UU l} {u : sequence A}
  (H : has-modulus-eventually-constant-sequence u)
  where

  value-has-modulus-eventually-constant-sequence : A
  value-has-modulus-eventually-constant-sequence =
    u (modulus-has-modulus-eventually-pointed-sequence H)

  is-eventual-value-has-modulus-eventually-constant-sequence :
    has-modulus-eventually-pointed-sequence
      (λ n → value-has-modulus-eventually-constant-sequence ＝ u n)
  is-eventual-value-has-modulus-eventually-constant-sequence =
    value-at-modulus-has-modulus-eventually-pointed-sequence H
```

## Properties

### Constant sequences are eventually constant

```agda
module _
  {l : Level} {A : UU l} (x : A)
  where

  has-modulus-eventually-constant-const-sequence :
    has-modulus-eventually-constant-sequence (const ℕ x)
  pr1 has-modulus-eventually-constant-const-sequence = zero-ℕ
  pr2 has-modulus-eventually-constant-const-sequence p I =
    (zero-ℕ , λ _ _ → refl)
```

### An eventually constant sequence is eventually equal to the constant sequence of its eventual value

```agda
module _
  {l : Level} {A : UU l} {u : sequence A}
  (H : has-modulus-eventually-constant-sequence u)
  where

  has-modulus-eventually-eq-value-has-modulus-eventually-constant-sequence :
    has-modulus-eventually-eq-sequence
      ( const ℕ (value-has-modulus-eventually-constant-sequence H))
      ( u)
  has-modulus-eventually-eq-value-has-modulus-eventually-constant-sequence =
    is-eventual-value-has-modulus-eventually-constant-sequence H
```
