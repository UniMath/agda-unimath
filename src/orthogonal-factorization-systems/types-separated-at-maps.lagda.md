# Types separated at maps

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module orthogonal-factorization-systems.types-separated-at-maps
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types funext
open import foundation.universe-levels

open import orthogonal-factorization-systems.types-local-at-maps funext univalence truncations
```

</details>

## Idea

A type `A` is said to be **separated** with respect to a map `f`, or
**`f`-separated**, if its [identity types](foundation-core.identity-types.md)
are [`f`-local](orthogonal-factorization-systems.types-local-at-maps.md).

## Definitions

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-map-separated-family : (X → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  is-map-separated-family A = (x : X) (y z : A x) → is-local f (y ＝ z)

  is-map-separated : UU l3 → UU (l1 ⊔ l2 ⊔ l3)
  is-map-separated A = is-map-separated-family (λ _ → A)
```

## References

{{#bibliography}} {{#reference Rij19}}
