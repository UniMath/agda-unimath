# Pointwise extensions of families of globular types

```agda
{-# OPTIONS --guardedness #-}

module globular-types.pointwise-extensions-families-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import globular-types.dependent-globular-types
open import globular-types.globular-equivalences
open import globular-types.globular-types
open import globular-types.points-globular-types
```

</details>

## Idea

Consider a family of [globular types](globular-types.globular-types.md)
`H : G₀ → Globular-Type` indexed by the 0-cells of a globular type `G` and
consider a [dependent globular type](globular-types.dependent-globular-types.md)
`K` over `G`. We say that `K` is a
{{#concept "pointwise extension" Disambiguation="family of globular types" Agda=is-pointwise-extension-family-of-globular-types-Dependent-Globular-Type}}
of `H` if it comes equipped with a family of
[globular equivalences](globular-types.globular-equivalences.md)

```text
  ev-point K x ≃ H x₀
```

indexed by the [points](globular-types.points-globular-types.md) of `G`.

## Definitions

### The predicate of being a pointwise extension of a family of globular types

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} {G : Globular-Type l1 l2}
  (H : 0-cell-Globular-Type G → Globular-Type l3 l4)
  (K : Dependent-Globular-Type l5 l6 G)
  where

  is-pointwise-extension-family-of-globular-types-Dependent-Globular-Type :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  is-pointwise-extension-family-of-globular-types-Dependent-Globular-Type =
    (x : point-Globular-Type G) →
    globular-equiv
      ( ev-point-Dependent-Globular-Type K x)
      ( H (0-cell-point-Globular-Type x))
```

### The type of pointwise extensions of a family of globular types

```agda
module _
  {l1 l2 l3 l4 : Level} (l5 l6 : Level) (G : Globular-Type l1 l2)
  (H : 0-cell-Globular-Type G → Globular-Type l3 l4)
  where

  pointwise-extension-family-of-globular-types :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5 ⊔ lsuc l6)
  pointwise-extension-family-of-globular-types =
    Σ ( Dependent-Globular-Type l5 l6 G)
      ( is-pointwise-extension-family-of-globular-types-Dependent-Globular-Type
        H)
```
