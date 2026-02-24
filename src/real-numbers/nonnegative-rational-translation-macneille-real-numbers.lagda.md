# Nonnegative rational translation on MacNeille real numbers

```agda
module real-numbers.nonnegative-rational-translation-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.inequality-macneille-real-numbers
open import real-numbers.macneille-real-numbers
open import real-numbers.raising-universe-levels-located-macneille-real-numbers
open import real-numbers.rational-translation-macneille-real-numbers
open import real-numbers.translation-macneille-real-numbers
```

</details>

## Theorems

```agda
abstract
  leq-self-translate-raise-ℚ⁰⁺-macneille-ℝ :
    {l : Level} →
    (x : macneille-ℝ l) →
    (q : ℚ⁰⁺) →
    leq-macneille-ℝ
      ( x)
      ( translate-macneille-ℝ
        ( raise-located-macneille-real-ℚ l (rational-ℚ⁰⁺ q))
        ( x))
  leq-self-translate-raise-ℚ⁰⁺-macneille-ℝ {l} x q =
    tr
      ( λ y →
        leq-macneille-ℝ
          ( y)
          ( translate-macneille-ℝ
            ( raise-located-macneille-real-ℚ l (rational-ℚ⁰⁺ q))
            ( x)))
      ( left-raise-zero-law-translate-macneille-ℝ x)
      ( preserves-leq-translate-raise-ℚ-macneille-ℝ
        ( x)
        ( zero-ℚ)
        ( rational-ℚ⁰⁺ q)
        ( leq-zero-rational-ℚ⁰⁺ q))
```
