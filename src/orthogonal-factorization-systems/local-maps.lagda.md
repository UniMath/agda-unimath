# Local maps

```agda
module orthogonal-factorization-systems.local-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-families-of-types
open import orthogonal-factorization-systems.local-types
```

</details>

## Idea

A map `g : A → B` is said to be **local at** `f : Y → X`, or **`f`-local**, if
all its [fibers](foundation-core.fibers-of-maps.md) are. Likewise, a family
`B : A → UU l` is local at `f` if each `B x` is.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} {Y : UU l1} {X : UU l2} {A : UU l3} {B : UU l4}
  (f : Y → X) (g : A → B)
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
  {l1 l2 l3 : Level} {Y : UU l1} {X : UU l2} {B : UU l3}
  (f : Y → X)
  where

  is-local-is-local-terminal-map :
    is-local-map f (terminal-map {A = B}) → is-local f B
  is-local-is-local-terminal-map H =
    is-local-equiv f (inv-equiv-fiber-terminal-map star) (H star)

  is-local-terminal-map-is-local :
    is-local f B → is-local-map f (terminal-map {A = B})
  is-local-terminal-map-is-local H u =
    is-local-equiv f (equiv-fiber-terminal-map u) H
```

### A map is `f`-local if and only if it is `f`-orthogonal

This remains to be formalized.

## See also

- [Localizations with respect to maps](orthogonal-factorization-systems.localizations-maps.md)
- [Localizations with respect to subuniverses](orthogonal-factorization-systems.localizations-subuniverses.md)
