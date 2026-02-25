# Irrational real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.irrational-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

An
{{#concept "irrational real number" WDID=Q607728 WD="irrational number" Agda=is-irrational-ℝ}}
is a [real number](real-numbers.dedekind-real-numbers.md) that is not
[rational](real-numbers.rational-real-numbers.md).

## Definition

```agda
is-irrational-prop-ℝ : {l : Level} → ℝ l → Prop l
is-irrational-prop-ℝ x = ¬' (subtype-rational-ℝ x)

is-irrational-ℝ : {l : Level} → ℝ l → UU l
is-irrational-ℝ x = type-Prop (is-irrational-prop-ℝ x)
```
