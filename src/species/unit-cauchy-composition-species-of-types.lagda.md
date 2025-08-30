# The unit of Cauchy composition of species of types

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

The
{{#concept "unit" Disambiguation="of Cauchy composition of species of types" Agda=unit-species-types}}
of [Cauchy composition](species.cauchy-composition-species-of-types.md) of
[species of types](species.species-of-types.md) is the species

```text
  X ↦ is-contr X.
```

## Definition

```agda
unit-species-types : {l1 : Level} → species-types l1 l1
unit-species-types = is-contr
```
