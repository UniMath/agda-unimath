# Maps local at maps

```agda
module orthogonal-factorization-systems.maps-local-at-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-morphisms-arrows
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-fibers-of-maps
open import foundation.homotopies
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.pullbacks
open import foundation.unit-type
open import foundation.universal-property-family-of-fibers-of-maps
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-families-of-types
open import orthogonal-factorization-systems.orthogonal-maps
open import orthogonal-factorization-systems.pullback-hom
open import orthogonal-factorization-systems.types-local-at-maps
```

</details>

## Idea

A map `g : X → Y` is said to be
{{#concept "local" Disambiguation="maps of types" Agda=is-local-map}} at
`f : A → B`, or
{{#concept "`f`-local" Disambiguation="maps of types" Agda=is-local-map}}, if
all its [fibers](foundation-core.fibers-of-maps.md) are
[`f`-local types](orthogonal-factorization-systems.types-local-at-maps.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-local-map : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-local-map = is-local-family f (fiber g)

  is-property-is-local-map : is-prop is-local-map
  is-property-is-local-map = is-property-is-local-family f (fiber g)

  is-local-map-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-local-map-Prop = is-local-family-Prop f (fiber g)
```

### A type `B` is `f`-local if and only if the terminal map `B → unit` is `f`-local

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {Y : UU l3}
  (f : A → B)
  where

  is-local-is-local-terminal-map :
    is-local-map f (terminal-map Y) → is-local f Y
  is-local-is-local-terminal-map H =
    is-local-equiv f (inv-equiv-fiber-terminal-map star) (H star)

  is-local-terminal-map-is-local :
    is-local f Y → is-local-map f (terminal-map Y)
  is-local-terminal-map-is-local H u =
    is-local-equiv f (equiv-fiber-terminal-map u) H
```

### A map is `f`-local if it is `f`-orthogonal

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-local-map-is-orthogonal-pullback-condition :
    is-orthogonal-pullback-condition f g → is-local-map f g
  is-local-map-is-orthogonal-pullback-condition G y =
    is-local-is-orthogonal-pullback-condition-terminal-map f
      ( is-orthogonal-pullback-condition-right-base-change f g
        ( terminal-map (fiber g y))
        ( fiber-cartesian-hom-arrow g y)
        ( G))

  is-local-map-is-orthogonal : is-orthogonal f g → is-local-map f g
  is-local-map-is-orthogonal G y =
    is-local-is-orthogonal-terminal-map f
      ( is-orthogonal-right-base-change f g
        ( terminal-map (fiber g y))
        ( fiber-cartesian-hom-arrow g y)
        ( G))
```

### `f`-local maps are closed under base change

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

## See also

- [Localizations with respect to maps](orthogonal-factorization-systems.localizations-at-maps.md)
- [Localizations with respect to subuniverses](orthogonal-factorization-systems.localizations-at-subuniverses.md)
