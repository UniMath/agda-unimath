# Trivial real vector spaces

```agda
module linear-algebra.trivial-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.real-vector-spaces
open import linear-algebra.trivial-left-modules-rings

open import real-numbers.large-ring-of-real-numbers
```

</details>

## Idea

The
{{#concept "trivial vector space" Disambiguation="over ℝ" Agda=trivial-ℝ-Vector-Space}}
over the [real numbers](real-numbers.dedekind-real-numbers.md) is the
[real vector space](linear-algebra.real-vector-spaces.md) consisting of exactly
one element, `0`.

## Properties

### The property of being a trivial vector space

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Vector-Space l1 l2)
  where

  is-trivial-prop-ℝ-Vector-Space : Prop l2
  is-trivial-prop-ℝ-Vector-Space =
    is-trivial-prop-left-module-Ring (ring-ℝ l1) V

  is-trivial-ℝ-Vector-Space : UU l2
  is-trivial-ℝ-Vector-Space = type-Prop is-trivial-prop-ℝ-Vector-Space
```

### The trivial real vector space

```agda
module _
  (l : Level)
  where

  trivial-ℝ-Vector-Space : ℝ-Vector-Space l lzero
  trivial-ℝ-Vector-Space = trivial-left-module-Ring (ring-ℝ l)

  is-trivial-trivial-ℝ-Vector-Space :
    is-trivial-ℝ-Vector-Space trivial-ℝ-Vector-Space
  is-trivial-trivial-ℝ-Vector-Space =
    is-trivial-trivial-left-module-Ring (ring-ℝ l)
```
