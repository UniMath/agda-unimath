# Coalgebras of the maybe monad

```agda
module foundation.coalgebras-maybe where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.maybe
open import foundation.universe-levels

open import trees.polynomial-endofunctors
```

</details>

## Idea

A
{{#concept "coalgebra" Disambiguation="of the maybe monad" Agda=coalgebra-Maybe}}
is a type `X` [equipped](foundation.structure.md) with a map

```text
  X → Maybe X.
```

## Definitions

### Maybe-coalgebra structure on a type

```agda
coalgebra-structure-Maybe : {l : Level} → UU l → UU l
coalgebra-structure-Maybe X = X → Maybe X
```

### Maybe-coalgebras

```agda
coalgebra-Maybe : (l : Level) → UU (lsuc l)
coalgebra-Maybe l = Σ (UU l) (coalgebra-structure-Maybe)

module _
  {l : Level} (X : coalgebra-Maybe l)
  where

  type-coalgebra-Maybe : UU l
  type-coalgebra-Maybe = pr1 X

  map-coalgebra-Maybe : type-coalgebra-Maybe → Maybe type-coalgebra-Maybe
  map-coalgebra-Maybe = pr2 X
```

### Coalgebra map

```agda
-- coalgebra-structure-map-Maybe :
--   {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} → coalgebra-structure-Maybe X → (Y → X) → coalgebra-structure-Maybe Y
-- coalgebra-structure-map-Maybe f g = {!   !}
```
