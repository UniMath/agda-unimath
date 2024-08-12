# Maps in global subuniverses

```agda
module foundation.maps-in-global-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-morphisms-arrows
open import foundation.dependent-pair-types
open import foundation.functoriality-fibers-of-maps
open import foundation.global-subuniverses
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.propositions
```

</details>

## Idea

Given a [global subuniverse](foundation.global-subuniverses.md) `𝒫` a map
`f : A → B` is said to be a
`𝒫`-{{#concept "map" Disambiguation="in a global subuniverse" Agda=is-in-global-subuniverse-map}},
or to be a map in `𝒫` if its [fibers](foundation-core.fibers-of-maps.md) are in
`𝒫`.

## Definitions

### Maps in a global subuniverse

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-in-global-subuniverse-map : UU (α (l1 ⊔ l2) ⊔ l2)
  is-in-global-subuniverse-map =
    (b : B) → is-in-global-subuniverse 𝒫 (fiber f b)

  is-prop-is-in-global-subuniverse-map : is-prop is-in-global-subuniverse-map
  is-prop-is-in-global-subuniverse-map =
    is-prop-Π (λ b → is-prop-is-in-global-subuniverse 𝒫 (fiber f b))

  is-in-global-subuniverse-map-Prop : Prop (α (l1 ⊔ l2) ⊔ l2)
  is-in-global-subuniverse-map-Prop =
    ( is-in-global-subuniverse-map , is-prop-is-in-global-subuniverse-map)
```

## Properties

### Closure under base change

Maps in `𝒫` are closed under base change.

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D)
  where

  is-in-global-subuniverse-map-base-change :
    is-in-global-subuniverse-map 𝒫 f →
    cartesian-hom-arrow g f →
    is-in-global-subuniverse-map 𝒫 g
  is-in-global-subuniverse-map-base-change F α d =
    is-closed-under-equiv-global-subuniverse 𝒫 (l1 ⊔ l2) (l3 ⊔ l4)
    ( fiber f (map-codomain-cartesian-hom-arrow g f α d))
    ( fiber g d)
    ( inv-equiv (equiv-fibers-cartesian-hom-arrow g f α d))
    ( F (map-codomain-cartesian-hom-arrow g f α d))
```
