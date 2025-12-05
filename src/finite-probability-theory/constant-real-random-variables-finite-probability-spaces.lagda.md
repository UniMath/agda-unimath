# Constnant real random variables in finite probability spaces

```agda
module finite-probability-theory.constant-real-random-variables-finite-probability-spaces where
```

<details><summary>Imports</summary>

```agda
open import finite-probability-theory.finite-probability-spaces
open import finite-probability-theory.real-random-variables-finite-probability-spaces

open import foundation.universe-levels

open import group-theory.sums-of-finite-families-of-elements-abelian-groups

open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

Any [real number](real-numbers.dedekind-real-numbers.md) `x` defines a
{{#concept "constant real random variable" Disambiguation="in a finite probability space" Agda=const-real-random-variable-Finite-Probability-Space}}
on any
[finite probability space](finite-probability-theory.finite-probability-spaces.md)
`Ω`: the
[real random variable](finite-probability-theory.real-random-variables-finite-probability-spaces.md)
`X : (e : Ω) ↦ x`.

## Definitions

### Constant random variables in a finite probability space

```agda
module _
  {l1 l2 : Level} (Ω : Finite-Probability-Space l1 l2)
  where

  const-real-random-variable-Finite-Probablity-Space :
    (x : ℝ l2) → real-random-variable-Finite-Probability-Space l2 Ω
  const-real-random-variable-Finite-Probablity-Space x _ = x
```
