# Functoriality of the pullback-hom

```agda
module orthogonal-factorization-systems.functoriality-pullback-hom where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-types
open import foundation.functoriality-pullbacks
open import foundation.morphisms-arrows
open import foundation.morphisms-cospan-diagrams
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.universe-levels

open import orthogonal-factorization-systems.pullback-hom
```

</details>

## Idea

The construction of the
[pullback-hom](orthogonal-factorization-systems.pullback-hom.md) is functorial.

## Definition

### Functorial action on maps of the pullback-hom

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  {l1' l2' l3' l4' : Level}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {Y' : UU l4'}
  (f' : A' → B') (g' : X' → Y')
  where

  map-pullback-hom :
    hom-cospan-diagram
      ( precomp f' Y')
      ( postcomp A' g')
      ( precomp f Y)
      ( postcomp A g) →
    hom-arrow f' g' → hom-arrow f g
  map-pullback-hom =
    map-is-pullback
      ( precomp f Y)
      ( postcomp A g)
      ( precomp f' Y')
      ( postcomp A' g')
      ( cone-hom-arrow-pullback-hom f g)
      ( cone-hom-arrow-pullback-hom f' g')
      ( is-pullback-cone-hom-arrow-pullback-hom f g)
      ( is-pullback-cone-hom-arrow-pullback-hom f' g')
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
