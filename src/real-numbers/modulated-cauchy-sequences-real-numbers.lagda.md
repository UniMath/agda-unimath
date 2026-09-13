# Modulated Cauchy sequences in the real numbers

```agda
module real-numbers.modulated-cauchy-sequences-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.modulated-cauchy-sequences-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
```

</details>

## Idea

A
{{#concept "modulated Cauchy sequence" Disambiguation="in ℝ" Agda=modulated-cauchy-sequence-ℝ}}
in the [real numbers](real-numbers.dedekind-real-numbers.md) is a
[modulated Cauchy sequence](metric-spaces.modulated-cauchy-sequences-metric-spaces.md)
in the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md)

## Definition

```agda
cauchy-modulus-sequence-ℝ : {l : Level} → sequence (ℝ l) → UU l
cauchy-modulus-sequence-ℝ {l} =
  cauchy-modulus-sequence-Metric-Space (metric-space-ℝ l)

modulated-cauchy-sequence-ℝ : (l : Level) → UU (lsuc l)
modulated-cauchy-sequence-ℝ l =
  modulated-cauchy-sequence-Metric-Space (metric-space-ℝ l)
```
