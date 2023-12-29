# The universal property of pullbacks

```agda
module foundation.universal-property-pullbacks where

open import foundation-core.universal-property-pullbacks public
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.propositions
```

</details>

## Idea

The universal property of pullbacks describes the optimal way to complete a
diagram of the form

```text
         B
         |
         |
         V
A -----> X
```

to a square

```text
C -----> B
| ⌟      |
|        |
V        V
A -----> X
```

## Properties

### The homotopy of cones obtained from the universal property of pullbacks

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4}
  where

  htpy-cone-map-universal-property-pullback :
    (c : cone f g C) (up : universal-property-pullback f g c) →
    {l5 : Level} {C' : UU l5} (c' : cone f g C') →
    htpy-cone f g
      ( cone-map f g c (map-universal-property-pullback f g c up c'))
      ( c')
  htpy-cone-map-universal-property-pullback c up c' =
    htpy-eq-cone f g
      ( cone-map f g c (map-universal-property-pullback f g c up c'))
      ( c')
      ( compute-map-universal-property-pullback f g c up c')
```

### Uniquely uniqueness of pullbacks

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} {C' : UU l5}
  where

  abstract
    uniquely-unique-pullback :
      ( c' : cone f g C') (c : cone f g C) →
      ( up-c' : universal-property-pullback f g c') →
      ( up-c : universal-property-pullback f g c) →
      is-contr
        ( Σ (C' ≃ C) (λ e → htpy-cone f g (cone-map f g c (map-equiv e)) c'))
    uniquely-unique-pullback c' c up-c' up-c =
      is-torsorial-Eq-subtype
        ( uniqueness-universal-property-pullback f g c up-c C' c')
        ( is-property-is-equiv)
        ( map-universal-property-pullback f g c up-c c')
        ( htpy-cone-map-universal-property-pullback f g c up-c c')
        ( is-equiv-up-pullback-up-pullback c c'
          ( map-universal-property-pullback f g c up-c c')
          ( htpy-cone-map-universal-property-pullback f g c up-c c')
          up-c up-c')
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
