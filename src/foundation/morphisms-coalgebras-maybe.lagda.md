# Morphisms of coalgebras of the maybe monad

```agda
module foundation.morphisms-coalgebras-maybe where
```

<details><summary>Imports</summary>

```agda
open import foundation.coalgebras-maybe
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.maybe

open import trees.polynomial-endofunctors
```

</details>

## Idea

Given two [coalgebras](foundation.coalgebras-maybe.md) of the
[maybe monad](foundation-core.maybe.md) `η : X → Maybe X`, `η' : Y → Maybe Y`,
then a map `f : X → Y` is a
{{#concept "morphism of coalgebras" Disambiguation="of the maybe monad" Agda=hom-coalgebra-Maybe}}
if the square

```text
            f
     X ----------> Y
     |             |
     |             |
     ∨             ∨
  Maybe X ----> Maybe Y
         Maybe f
```

[commutes](foundation.commuting-squares-of-maps.md).

## Definitions

```agda
coherence-hom-coalgebra-Maybe :
  {l1 l2 : Level} (X : coalgebra-Maybe l1) (Y : coalgebra-Maybe l2) →
  (type-coalgebra-Maybe X → type-coalgebra-Maybe Y) → UU (l1 ⊔ l2)
coherence-hom-coalgebra-Maybe X Y f =
  coherence-square-maps
    ( f)
    ( map-coalgebra-Maybe X)
    ( map-coalgebra-Maybe Y)
    ( map-Maybe f)

hom-coalgebra-Maybe :
  {l1 l2 : Level} (X : coalgebra-Maybe l1) (Y : coalgebra-Maybe l2) →
  UU (l1 ⊔ l2)
hom-coalgebra-Maybe X Y =
  Σ ( type-coalgebra-Maybe X → type-coalgebra-Maybe Y)
    ( coherence-hom-coalgebra-Maybe X Y)

module _
  {l1 l2 : Level} (X : coalgebra-Maybe l1) (Y : coalgebra-Maybe l2)
  (f : hom-coalgebra-Maybe X Y)
  where

  map-hom-coalgebra-Maybe : type-coalgebra-Maybe X → type-coalgebra-Maybe Y
  map-hom-coalgebra-Maybe = pr1 f

  coh-hom-coalgebra-Maybe :
    coherence-hom-coalgebra-Maybe X Y map-hom-coalgebra-Maybe
  coh-hom-coalgebra-Maybe = pr2 f
```
