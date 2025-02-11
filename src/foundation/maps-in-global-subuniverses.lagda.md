# Maps in global subuniverses

```agda
module foundation.maps-in-global-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-morphisms-arrows
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.functoriality-fibers-of-maps
open import foundation.global-subuniverses
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.propositions
```

</details>

## Idea

Given a [global subuniverse](foundation.global-subuniverses.md) `𝒫`, a map
`f : A → B` is said to be a
{{#concept "map in `𝒫`" Disambiguation="in a global subuniverse" Agda=is-in-global-subuniverse-map}},
or a **`𝒫`-map**, if its [fibers](foundation-core.fibers-of-maps.md) are in `𝒫`.

## Definitions

### The predicate on maps of being in a global subuniverse

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

### A type is in `𝒫` if and only if its terminal projection is in `𝒫`

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 : Level} {A : UU l1}
  where

  is-in-global-subuniverse-is-in-global-subuniverse-terminal-map :
    is-in-global-subuniverse-map 𝒫 (terminal-map A) →
    is-in-global-subuniverse 𝒫 A
  is-in-global-subuniverse-is-in-global-subuniverse-terminal-map H =
    is-closed-under-equiv-global-subuniverse 𝒫
      ( fiber (terminal-map A) star)
      ( A)
      ( equiv-fiber-terminal-map star)
      ( H star)

  is-in-global-subuniverse-terminal-map-is-in-global-subuniverse :
    is-in-global-subuniverse 𝒫 A →
    is-in-global-subuniverse-map 𝒫 (terminal-map A)
  is-in-global-subuniverse-terminal-map-is-in-global-subuniverse H u =
    is-closed-under-equiv-global-subuniverse 𝒫
      ( A)
      ( fiber (terminal-map A) u)
      ( inv-equiv-fiber-terminal-map u)
      ( H)
```

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
    is-closed-under-equiv-global-subuniverse 𝒫
      ( fiber f (map-codomain-cartesian-hom-arrow g f α d))
      ( fiber g d)
      ( inv-equiv (equiv-fibers-cartesian-hom-arrow g f α d))
      ( F (map-codomain-cartesian-hom-arrow g f α d))
```
