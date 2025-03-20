# Maps local at maps

```agda
open import foundation.function-extensionality-axiom

module
  orthogonal-factorization-systems.maps-local-at-maps
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-morphisms-arrows funext
open import foundation.fibers-of-maps funext
open import foundation.propositions funext
open import foundation.retracts-of-maps funext
open import foundation.unit-type
open import foundation.universe-levels

open import orthogonal-factorization-systems.families-of-types-local-at-maps funext
open import orthogonal-factorization-systems.orthogonal-maps funext
open import orthogonal-factorization-systems.types-local-at-maps funext
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

Maps local at `f` are closed under base change.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} {E : UU l5} {F : UU l6}
  {f : A → B} {g : C → D} {g' : E → F}
  where

  is-local-map-base-change :
    is-local-map f g → cartesian-hom-arrow g' g → is-local-map f g'
  is-local-map-base-change G α d =
    is-local-equiv f
      ( equiv-fibers-cartesian-hom-arrow g' g α d)
      ( G (map-codomain-cartesian-hom-arrow g' g α d))
```

### `f`-local maps are closed under retracts

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} {E : UU l5} {F : UU l6}
  {f : A → B} {g : C → D} {g' : E → F}
  where

  is-local-retract-map :
    is-local-map f g → g' retract-of-map g → is-local-map f g'
  is-local-retract-map G R d =
    is-local-retract
      ( retract-fiber-retract-map g' g R d)
      ( G (map-codomain-inclusion-retract-map g' g R d))
```

## See also

- [Localizations with respect to maps](orthogonal-factorization-systems.localizations-at-maps.md)
- [Localizations with respect to subuniverses](orthogonal-factorization-systems.localizations-at-subuniverses.md)
