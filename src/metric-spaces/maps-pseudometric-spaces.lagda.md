# Maps between pseudometric spaces

```agda
module metric-spaces.maps-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.function-types
open import foundation.universe-levels

open import metric-spaces.pseudometric-spaces
```

</details>

## Idea

{{#concept "Maps" Disambiguation="between pseudometric spaces" Agda=map-Pseudometric-Space}}
between [pseudometric spaces](metric-spaces.pseudometric-spaces.md) are
functions between their carrier types.

## Definitions

### The type of maps between pseudometric spaces

```agda
module _
  {lx lx' ly ly' : Level}
  (X : Pseudometric-Space lx lx') (Y : Pseudometric-Space ly ly')
  where

  map-Pseudometric-Space : UU (lx ⊔ ly)
  map-Pseudometric-Space =
    type-Pseudometric-Space X → type-Pseudometric-Space Y
```

### The identity map on a pseudometric space

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  id-map-Pseudometric-Space : map-Pseudometric-Space M M
  id-map-Pseudometric-Space = id
```

### Constant maps between pseudometric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (b : type-Pseudometric-Space B)
  where

  const-map-Pseudometric-Space : map-Pseudometric-Space A B
  const-map-Pseudometric-Space = const (type-Pseudometric-Space A) b
```
