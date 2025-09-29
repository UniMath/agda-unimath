# Map-separated types at subuniverses

```agda
module orthogonal-factorization-systems.map-separated-types-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.subuniverses
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions

open import orthogonal-factorization-systems.extensions-maps
```

</details>

## Idea

Consider a [subuniverse](foundation.subuniverses.md) `K` and a map `δ : X → Y`.
A type `A` is said to be
{{#concept "`K`-separated relative to `δ`" Agda=is-map-separated'}} if the type
of extensions of any map `f : X → A` along `δ` is in `K`.

## Definitions

### The predicate of being map-separated

```agda
module _
  {l1 l2 l3 : Level} (K : subuniverse l1 l2)
  {X : UU l1} {Y : UU l1} (δ : X → Y)
  where

  is-map-separated' : (A : UU l1) → UU (l1 ⊔ l2)
  is-map-separated' A = (f : X → A) → is-in-subuniverse K (extension δ f)

  is-prop-is-map-separated' :
    (A : UU l1) → is-prop (is-map-separated' A)
  is-prop-is-map-separated' A =
    is-prop-Π (λ f → is-prop-is-in-subuniverse K (extension δ f))

  is-map-separated'-Prop :
    (A : UU l1) → Prop (l1 ⊔ l2)
  is-map-separated'-Prop A =
    ( is-map-separated' A , is-prop-is-map-separated' A)
```

## See also

- [Map-separated types at global subuniverses](orthogonal-factorization-systems.map-separated-types-global-subuniverses.md)
