# Relative separations of types at subuniverses

```agda
module orthogonal-factorization-systems.relative-separations-types-subuniverses where
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
{{#concept "`K`-separated relative to `δ`" Agda=is-rel-separated'}} if the type
of extensions of any map `f : X → A` along `δ` is in `K`.

## Definitions

### The predicate of being rel-separated

```agda
module _
  {l1 l2 l3 : Level} (K : subuniverse l1 l2)
  {X : UU l1} {Y : UU l1} (δ : X → Y)
  where

  is-rel-separated' : (A : UU l1) → UU (l1 ⊔ l2)
  is-rel-separated' A = (f : X → A) → is-in-subuniverse K (extension δ f)

  is-prop-is-rel-separated' :
    (A : UU l1) → is-prop (is-rel-separated' A)
  is-prop-is-rel-separated' A =
    is-prop-Π (λ f → is-prop-is-in-subuniverse K (extension δ f))

  is-rel-separated'-Prop :
    (A : UU l1) → Prop (l1 ⊔ l2)
  is-rel-separated'-Prop A =
    ( is-rel-separated' A , is-prop-is-rel-separated' A)
```

## See also

- [Relative separations of types at global subuniverses](orthogonal-factorization-systems.relative-separations-types-global-subuniverses.md)
