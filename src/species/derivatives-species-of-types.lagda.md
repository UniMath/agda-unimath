# Derivatives of species

```agda
module species.derivatives-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.unit-type
open import foundation.universe-levels

open import species.species-of-types
```

</details>

## Idea

When we think of a [species of types](species.species-of-types.md) as the
coefficients of a formal power series, the
{{#concept "derivative" Disambiguation="of species of types" Agda=derivative-species-types}}
of a species of types is the species of types representing the derivative of
that formal power series.

## Definition

```agda
derivative-species-types :
  {l1 l2 : Level} → species-types l1 l2 → species-types l1 l2
derivative-species-types F X = F (X + unit)
```
