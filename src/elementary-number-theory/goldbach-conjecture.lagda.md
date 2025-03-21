# The Goldbach conjecture

```agda
module elementary-number-theory.goldbach-conjecture where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.prime-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "Goldbach conjecture" WD="Goldbach's conjecture" WDID=Q485520 Agda=Goldbach-conjecture}}
states that every even
[natural number](elementary-number-theory.natural-numbers.md) `n`
[greater than](elementary-number-theory.strict-inequality-natural-numbers.md)
two is [equal](foundation-core.identity-types.md) to a
[sum](elementary-number-theory.addition-natural-numbers.md) of two
[primes](elementary-number-theory.prime-numbers.md)

```text
  n = p + q.
```

## Conjecture

```agda
Goldbach-conjecture : UU lzero
Goldbach-conjecture =
  ( n : ℕ) → (le-ℕ 2 n) → (is-even-ℕ n) →
    Σ ℕ (λ p → (is-prime-ℕ p) × (Σ ℕ (λ q → (is-prime-ℕ q) × (p +ℕ q ＝ n))))
```

## External links

- [Goldbach conjecture](https://www.britannica.com/science/Goldbach-conjecture)
  at Britannica
- [Goldbach's conjecture](https://en.wikipedia.org/wiki/Goldbach%27s_conjecture)
  at Wikipedia
- [Goldbach Conjecture](https://mathworld.wolfram.com/GoldbachConjecture.html)
  at Wolfram MathWorld
