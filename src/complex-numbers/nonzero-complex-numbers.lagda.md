# Nonzero complex numbers

```agda
module complex-numbers.nonzero-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import foundation.universe-levels
open import foundation.propositions
open import complex-numbers.apartness-complex-numbers
```

</details>

## Idea

A [complex number](complex-numbers.complex-numbers.md) is
{{#concept "nonzero" Agda=is-nonzero-ℂ}} if it is
[apart](complex-numbers.apartness-complex-numbers.md) from zero, that is, its
[real](real-numbers.dedekind-real-numbers.md) part
[or](foundation.disjunction.md) its imaginary part are
[nonzero](real-numbers.nonzero-real-numbers.md).

## Definition

```agda
is-nonzero-prop-ℂ : {l : Level} → ℂ l → Prop l
is-nonzero-prop-ℂ z = apart-prop-ℂ z zero-ℂ

is-nonzero-ℂ : {l : Level} → ℂ l → UU l
is-nonzero-ℂ z = type-Prop (is-nonzero-prop-ℂ z)
```
