# Nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

A real number `x` is
{{#concept "nonnegative" Disambiguation="real number" Agda=is-nonnegative-ℝ}} if
`0 ≤ x`.

## Definitions

```agda
is-nonnegative-ℝ : {l : Level} → ℝ l → UU l
is-nonnegative-ℝ = leq-ℝ zero-ℝ

is-nonnegative-prop-ℝ : {l : Level} → ℝ l → Prop l
is-nonnegative-prop-ℝ = leq-ℝ-Prop zero-ℝ

nonnegative-ℝ : (l : Level) → UU (lsuc l)
nonnegative-ℝ l = type-subtype (is-nonnegative-prop-ℝ {l})
```
