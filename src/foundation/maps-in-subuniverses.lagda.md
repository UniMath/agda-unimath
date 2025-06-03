# Maps in subuniverses

```agda
module foundation.maps-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.homotopies
open import foundation.subuniverses
open import foundation.universe-levels

open import foundation-core.fibers-of-maps
```

</details>

## Idea

Given a [subuniverse](foundation.subuniverses.md) `𝒫`, a map `f : A → B` is said
to be a
{{#concept "map in `𝒫`" Disambiguation="in a subuniverse" Agda=is-in-subuniverse-map}},
or a **`𝒫`-map**, if its [fibers](foundation-core.fibers-of-maps.md) are in `𝒫`.

## Definitions

### The predicate on maps of being in a subuniverse

```agda
is-in-subuniverse-map :
  {l1 l2 l3 : Level} (P : subuniverse (l1 ⊔ l2) l3) {A : UU l1} {B : UU l2} →
  (A → B) → UU (l2 ⊔ l3)
is-in-subuniverse-map P {A} {B} f = (b : B) → is-in-subuniverse P (fiber f b)
```

## Properties

### Subuniverses are closed under homotopies of maps

```agda
module _
  {l1 l2 l3 : Level} (P : subuniverse (l1 ⊔ l2) l3) {A : UU l1} {B : UU l2}
  {f g : A → B}
  where

  is-in-subuniverse-map-htpy :
    f ~ g → is-in-subuniverse-map P f → is-in-subuniverse-map P g
  is-in-subuniverse-map-htpy H F y =
    is-in-subuniverse-equiv' P (equiv-fiber-htpy H y) (F y)
```

## See also

- [Maps in global subuniverses](foundation.maps-in-global-subuniverses.md)
