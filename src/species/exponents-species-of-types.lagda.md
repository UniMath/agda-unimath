# Exponents of species

```agda
module species.exponents-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import species.species-of-types
```

</details>

## Idea

The exponent of two species `F` and `G` is the pointwise exponent

## Definitions

### Exponents of species of types

```agda
function-species-types :
  {l1 l2 l3 : Level} → species-types l1 l2 → species-types l1 l3 → UU l1 → UU (l2 ⊔ l3)
function-species-types F G X = F X → G X
```
