# Derivatives of species

```agda
open import foundation.function-extensionality-axiom

module
  species.derivatives-species-of-types
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types funext
open import foundation.unit-type
open import foundation.universe-levels

open import species.species-of-types funext
```

</details>

## Idea

When we think of a species of types as the coefficients of a formal power
series, the derivative of a species of types is the species of types
representing the derivative of that formal power series.

## Definition

```agda
derivative-species-types :
  {l1 l2 : Level} → species-types l1 l2 → species-types l1 l2
derivative-species-types F X = F (X + unit)
```
