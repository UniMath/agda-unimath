# multiplication on the rationals

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.multiplication-rationals where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions

open import foundation.dependent-pair-types
open import foundation.identity-types
```

</details>

## Idea

```

add-ℚ : ℚ → ℚ → ℚ
mul-ℚ (x , p) (y , q) = in-fraction-ℤ (add-fraction-ℤ x y)

```
