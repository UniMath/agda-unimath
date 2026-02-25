# Morphisms of wild monoids

```agda
module structured-types.morphisms-wild-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups

open import structured-types.morphisms-h-spaces
open import structured-types.pointed-maps
open import structured-types.wild-monoids
```

</details>

## Idea

{{#concept "Morphisms" Disambiguation="of wild monoids" Agda=hom-Wild-Monoid}}
between two [wild monoids](structured-types.wild-monoids.md) are maps that
preserve the unit and multiplication. We only require the unit and
multiplication to be preserved. This is because we would need further coherence
in wild monoids if we want morphisms to preserve the unital associator.

## Definition

### Homomorphisms of wild monoids

```agda
module _
  {l1 l2 : Level} (M : Wild-Monoid l1) (N : Wild-Monoid l2)
  where

  hom-Wild-Monoid : UU (l1 ⊔ l2)
  hom-Wild-Monoid =
    hom-H-Space
      ( h-space-Wild-Monoid M)
      ( h-space-Wild-Monoid N)

  pointed-map-hom-Wild-Monoid :
    hom-Wild-Monoid →
    pointed-type-Wild-Monoid M →∗ pointed-type-Wild-Monoid N
  pointed-map-hom-Wild-Monoid f = pr1 f

  map-hom-Wild-Monoid :
    hom-Wild-Monoid → type-Wild-Monoid M → type-Wild-Monoid N
  map-hom-Wild-Monoid f = pr1 (pr1 f)

  preserves-unit-map-hom-Wild-Monoid :
    (f : hom-Wild-Monoid) →
    (map-hom-Wild-Monoid f (unit-Wild-Monoid M)) ＝ (unit-Wild-Monoid N)
  preserves-unit-map-hom-Wild-Monoid f = pr2 (pr1 f)

  preserves-unital-mul-map-hom-Wild-Monoid :
    (f : hom-Wild-Monoid) →
    preserves-unital-mul-pointed-map-H-Space
      ( h-space-Wild-Monoid M)
      ( h-space-Wild-Monoid N)
      ( pointed-map-hom-Wild-Monoid f)
  preserves-unital-mul-map-hom-Wild-Monoid f = pr2 f

  preserves-mul-hom-Wild-Monoid :
    (f : hom-Wild-Monoid) →
    preserves-mul
      ( mul-Wild-Monoid M)
      ( mul-Wild-Monoid N)
      ( map-hom-Wild-Monoid f)
  preserves-mul-hom-Wild-Monoid f = pr1 (pr2 f)

  preserves-left-unit-law-mul-map-hom-Wild-Monoid :
    ( f : hom-Wild-Monoid) →
    preserves-left-unit-law-mul-pointed-map-H-Space
      ( h-space-Wild-Monoid M)
      ( h-space-Wild-Monoid N)
      ( pointed-map-hom-Wild-Monoid f)
      ( preserves-mul-hom-Wild-Monoid f)
  preserves-left-unit-law-mul-map-hom-Wild-Monoid f =
    pr1 (pr2 (pr2 f))

  preserves-right-unit-law-mul-map-hom-Wild-Monoid :
    (f : hom-Wild-Monoid) →
    preserves-right-unit-law-mul-pointed-map-H-Space
      ( h-space-Wild-Monoid M)
      ( h-space-Wild-Monoid N)
      ( pointed-map-hom-Wild-Monoid f)
      ( preserves-mul-hom-Wild-Monoid f)
  preserves-right-unit-law-mul-map-hom-Wild-Monoid f =
    pr1 (pr2 (pr2 (pr2 f)))

  preserves-coh-unit-laws-map-hom-Wild-Monoid :
    (f : hom-Wild-Monoid) →
    preserves-coherence-unit-laws-mul-pointed-map-H-Space
      ( h-space-Wild-Monoid M)
      ( h-space-Wild-Monoid N)
      ( pointed-map-hom-Wild-Monoid f)
      ( preserves-mul-hom-Wild-Monoid f)
      ( preserves-left-unit-law-mul-map-hom-Wild-Monoid f)
      ( preserves-right-unit-law-mul-map-hom-Wild-Monoid f)
  preserves-coh-unit-laws-map-hom-Wild-Monoid f =
    pr2 (pr2 (pr2 (pr2 f)))
```
