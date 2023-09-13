# Local maps

```agda
module orthogonal-factorization-systems.local-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.fibers-of-maps
open import foundation.propositions
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-families
```

</details>

## Idea

A map `g : A → B` is said to be **local at** `f : Y → X`, or **`f`-local**, if
all its [fibers](foundation-core.fibers-of-maps.md) are. Likewise, a family
`B : A → UU l` is local at `f` if each `B x` is.

## Definition

```agda
module _
  where

  is-local-map :
    {l1 l2 l3 l4 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
    {A : UU l3} {B : UU l4} → (A → B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-local-map f g = is-local-family f (fiber g)
```

## Properties

### Being local is a property

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-property-is-local-map :
    {l3 l4 : Level} {A : UU l3} {B : UU l4}
    (g : A → B) → is-prop (is-local-map f g)
  is-property-is-local-map g = is-property-is-local-family f (fiber g)

  is-local-map-Prop :
    {l3 l4 : Level} {A : UU l3} {B : UU l4}
    (g : A → B) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-local-map-Prop g = is-local-family-Prop f (fiber g)
```

### A type `B` is `f`-local if and only if the terminal projection `B → unit` is `f`-local

This remains to be formalized.

### A map is `f`-local if and only if it is `f`-orthogonal

This remains to be formalized.

## See also

- [Localizations with respect to maps](orthogonal-factorization-systems.localizations-maps.md)
- [Localizations with respect to subuniverses](orthogonal-factorization-systems.localizations-subuniverses.md)
