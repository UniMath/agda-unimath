# Small universes

```agda
open import foundation.function-extensionality-axiom

module
  foundation.small-universes
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.small-types funext
```

</details>

## Idea

A [universe](foundation.universe-levels.md) `𝒰` is said to be
{{#concept "small" Disambiguation="universe of types" Agda=is-small-universe}}
with respect to `𝒱` if `𝒰` is a `𝒱`-[small](foundation-core.small-types.md) type
and each `X : 𝒰` is a `𝒱`-small type.

```agda
is-small-universe :
  (l l1 : Level) → UU (lsuc l1 ⊔ lsuc l)
is-small-universe l l1 = is-small l (UU l1) × ((X : UU l1) → is-small l X)
```
