# Real random variables in finite probability spaces

```agda
module finite-probability-theory.real-random-variables-finite-probability-spaces where
```

<details><summary>Imports</summary>

```agda
open import finite-probability-theory.finite-probability-spaces
open import finite-probability-theory.positive-distributions-on-finite-types
open import finite-probability-theory.probability-distributions-on-finite-types

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.sums-of-finite-families-of-elements-abelian-groups

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers

open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

A
{{#concept "real random variable" Disambiguation="in a finite probability space" Agda=random-real-variable-Finite-Probability-Space}}
in a
[finite probability space](finite-probability-theory.finite-probability-spaces.md)
is a function from the underlying
[finite type](univalent-combinatorics.finite-types.md) to
[`ℝ`](real-numbers.dedekind-real-numbers.md).

Our definition follows Definition 2.1 of {{#cite Babai00}}.

## Definitions

### Real random variables in a finite probability space

```agda
module _
  {l : Level} (Ω : Finite-Probability-Space l)
  where

  real-random-variable-Finite-Probability-Space : UU (lsuc lzero ⊔ l)
  real-random-variable-Finite-Probability-Space =
    type-Finite-Probability-Space Ω → ℝ lzero
```

### Constant random variables in a finite probability space

```agda
module _
  {l : Level} (Ω : Finite-Probability-Space l)
  where

  const-real-random-variable-Finite-Probablity-Space :
    (x : ℝ lzero) → real-random-variable-Finite-Probability-Space Ω
  const-real-random-variable-Finite-Probablity-Space x _ = x
```

### Atomic real random variables in a finite probability space

```agda
module _
  {l : Level} (Ω : Finite-Probability-Space l)
  (e : type-Finite-Probability-Space Ω)
  where

  atomic-real-random-variable-Finite-Probability-Space :
    real-random-variable-Finite-Probability-Space Ω
  atomic-real-random-variable-Finite-Probability-Space e' =
    rec-coproduct
      ( λ _ → one-ℝ)
      ( λ _ → zero-ℝ)
      ( has-decidable-equality-is-finite
        ( is-finite-type-Finite-Probability-Space Ω)
        ( e)
        ( e'))
```

## References

{{#bibliography}}
