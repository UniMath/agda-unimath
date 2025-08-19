# Functions between pseudometric spaces

```agda
module metric-spaces.functions-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-types
open import foundation.universe-levels

open import metric-spaces.pseudometric-spaces
```

</details>

## Idea

{{#concept "Functions" Disambiguation="between pseudometric spaces" Agda=type-function-Pseudometric-Space}}
between [pseudometric spaces](metric-spaces.pseudometric-spaces.md) are
functions between their carrier types.

## Definitions

### The type of functions between pseudometric spaces

```agda
module _
  {lx lx' ly ly' : Level}
  (X : Pseudometric-Space lx lx') (Y : Pseudometric-Space ly ly')
  where

  type-function-Pseudometric-Space : UU (lx ⊔ ly)
  type-function-Pseudometric-Space =
    type-Pseudometric-Space X → type-Pseudometric-Space Y
```

### The identity function on a pseudometric space

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  id-Pseudometric-Space : type-function-Pseudometric-Space M M
  id-Pseudometric-Space = id
```
