# Expected value of real random variables in finite probability spaces

```agda
module finite-probability-theory.expected-value-real-random-variables-finite-probability-spaces where
```

<details><summary>Imports</summary>

```agda
open import finite-probability-theory.finite-probability-spaces
open import finite-probability-theory.positive-distributions-on-finite-types
open import finite-probability-theory.probability-distributions-on-finite-types
open import finite-probability-theory.real-random-variables-finite-probability-spaces

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

open import univalent-combinatorics.finite-types
```

</details>

## Idea

The
{{#concept "expected value" Disambiguation="of a real random variable in a finite probability space" Agda=expected-value-real-random-variable-Finite-Probability-Space}}
of a
[real random variable](finite-probability-theory.real-random-variables-finite-probability-spaces.md)
`X` in a
[finite probability space](finite-probability-theory.finite-probability-spaces.md)
`(Ω , Pr)` is the
[sum](group-theory.sums-of-finite-families-of-elements-abelian-groups.md)

$$
  ∑_{x ∈ Ω} X(x)\operatorname{Pr}(x).
$$

Our definition follows Definition 2.2 of {{#cite Babai00}}.

## Definitions

### Expected value of a real random variable in a finite probability space

```agda
module _
  {l : Level} (Ω : Finite-Probability-Space l)
  (X : real-random-variable-Finite-Probability-Space Ω)
  where

  expected-value-real-random-variable-Finite-Probability-Space : ℝ lzero
  expected-value-real-random-variable-Finite-Probability-Space =
    sum-finite-Ab
      ( abelian-group-add-ℝ-lzero)
      ( finite-type-Finite-Probability-Space Ω)
      ( λ x →
        mul-ℝ
          ( X x)
          ( real-distribution-Finite-Probability-Space Ω x))
```

## References

{{#bibliography}}
