# Atomic real random variables in finite probability spaces

```agda
module finite-probability-theory.atomic-real-random-variables-finite-probability-spaces where
```

<details><summary>Imports</summary>

```agda
open import finite-probability-theory.finite-probability-spaces
open import finite-probability-theory.real-random-variables-finite-probability-spaces

open import foundation.coproduct-types
open import foundation.identity-types
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.rational-real-numbers

open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

The
{{#concept "atomic real random variable" Disambiguation="in a finite probability space" Agda=atomic-real-random-variable-Finite-Probability-Space}}
in a
[finite probability space](finite-probability-theory.finite-probability-spaces.md)
`(Ω , Pr)` at `e : Ω` is the
[real random variable](finite-probability-theory.real-random-variables-finite-probability-spaces.md)
`X : Ω → ℝ` such that:

- `X e ＝ 1`;
- `∀ (e' : Ω) (e' ≠ e) → X e ＝ 0`.

## Definition

### Atomic real random variables in a finite probability space

```agda
module _
  {l1 l2 : Level} (Ω : Finite-Probability-Space l1 l2)
  (e : type-Finite-Probability-Space Ω)
  where

  atomic-real-random-variable-Finite-Probability-Space :
    real-random-variable-Finite-Probability-Space lzero Ω
  atomic-real-random-variable-Finite-Probability-Space e' =
    rec-coproduct
      ( λ _ → one-ℝ)
      ( λ _ → zero-ℝ)
      ( has-decidable-equality-is-finite
        ( is-finite-type-Finite-Probability-Space Ω)
        ( e)
        ( e'))
```
