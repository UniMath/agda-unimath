# Functorialty of pullbacks

```agda
module foundation.functoriality-pullbacks where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-fibers-of-maps
open import foundation.identity-types
open import foundation.morphisms-cospans
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.diagonal-maps-of-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.pullbacks
open import foundation-core.universal-property-pullbacks
```

</details>

## Idea

The construction of the [standard pullback](foundation-core.pullbacks.md) is
functorial.

## Definitions

### The functorial action on maps of pullbacks

```agda
module _
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X')
  where

  map-standard-pullback :
    hom-cospan f' g' f g → standard-pullback f' g' → standard-pullback f g
  pr1 (map-standard-pullback (hA , _) (a' , _)) = hA a'
  pr1 (pr2 (map-standard-pullback (hA , hB , _) (a' , b' , _))) = hB b'
  pr2 (pr2 (map-standard-pullback (hA , hB , hX , HA , HB) (a' , b' , p'))) =
    HA a' ∙ ap hX p' ∙ inv (HB b')

  map-is-pullback :
    {l4 l4' : Level} {C : UU l4} {C' : UU l4'} →
    (c : cone f g C) (c' : cone f' g' C') →
    is-pullback f g c → is-pullback f' g' c' →
    hom-cospan f' g' f g → C' → C
  map-is-pullback c c' is-pb-c is-pb-c' h x =
    map-inv-is-equiv is-pb-c (map-standard-pullback h (gap f' g' c' x))
```
