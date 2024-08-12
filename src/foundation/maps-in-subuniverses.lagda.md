# Maps in subuniverses

```agda
module foundation.maps-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.subuniverses
open import foundation.universe-levels

open import foundation-core.fibers-of-maps
```

</details>

## Idea

Given a [subuniverse](foundation-core.subuniverses.md) `𝒫` a map `f : A → B` is
said to be a
`𝒫`-{{#concept "map" Disambiguation="in a subuniverse" Agda=is-in-subuniverse-map}},
or to be a map in `𝒫` if its [fibers](foundation-core.fibers-of-maps.md) are in
`𝒫`.

## Definitions

### Maps in a subuniverse

```agda
is-in-subuniverse-map :
  {l1 l2 l3 : Level} (P : subuniverse (l1 ⊔ l2) l3) {A : UU l1} {B : UU l2} →
  (A → B) → UU (l2 ⊔ l3)
is-in-subuniverse-map P {A} {B} f = (b : B) → is-in-subuniverse P (fiber f b)
```

## See also

- [Maps in a global subuniverse](foundation.maps-in-global-subuniverses.md)
