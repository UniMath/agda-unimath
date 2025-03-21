# Cartesian exponents of species

```agda
module species.cartesian-exponents-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import species.species-of-types
```

</details>

## Idea

The **Cartesian exponent** of two species `F` and `G` is the pointwise exponent
of `F` and `G`.

Note that we call such exponents cartesian to disambiguate from other notions of
exponents, such as
[Cauchy exponentials](species.cauchy-exponentials-species-of-types.md).

## Definitions

### Cartesian exponents of species of types

```agda
function-species-types :
  {l1 l2 l3 : Level} →
  species-types l1 l2 → species-types l1 l3 → species-types l1 (l2 ⊔ l3)
function-species-types F G X = F X → G X
```
