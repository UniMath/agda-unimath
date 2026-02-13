# Nonnegative rational translation on MacNeille real numbers

```agda
module real-numbers.nonnegative-rational-translation-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.addition-macneille-real-numbers
open import real-numbers.inequality-macneille-real-numbers
open import real-numbers.macneille-real-numbers
open import real-numbers.raising-universe-levels-located-macneille-real-numbers
open import real-numbers.rational-translation-macneille-real-numbers
```

</details>

## Theorems

```agda
abstract
  leq-right-translate-nonnegative-raise-macneille-real-ℚ :
    {l : Level} →
    (x : macneille-ℝ l) →
    (q : ℚ) →
    leq-ℚ zero-ℚ q →
    leq-macneille-ℝ
      ( x)
      ( add-macneille-ℝ (raise-located-macneille-real-ℚ l q) x)
  leq-right-translate-nonnegative-raise-macneille-real-ℚ {l} x q 0≤q =
    tr
      ( λ y →
        leq-macneille-ℝ
          ( y)
          ( add-macneille-ℝ (raise-located-macneille-real-ℚ l q) x))
      ( left-raise-zero-law-add-macneille-ℝ x)
      ( preserves-leq-left-add-raise-macneille-real-ℚ
        ( x)
        ( zero-ℚ)
        ( q)
        ( 0≤q))
```
