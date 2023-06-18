# The unit of Cauchy composition of types

```agda
module species.unit-cauchy-composition-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.universe-levels

open import species.species-of-types
```

</details>

## Idea

The **unit** of Cauchy composition of species of types is the species

```text
  X ↦ is-contr X.
```

## Definition

```agda
unit-species-types : {l1 : Level} → species-types l1 l1
unit-species-types = is-contr
```
