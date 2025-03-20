# Pointwise extensions of families of reflexive globular types

```agda
{-# OPTIONS --guardedness #-}

module
  globular-types.pointwise-extensions-families-reflexive-globular-types
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import globular-types.dependent-globular-types funext
open import globular-types.dependent-reflexive-globular-types funext
open import globular-types.globular-types
open import globular-types.points-globular-types funext
open import globular-types.points-reflexive-globular-types funext
open import globular-types.reflexive-globular-equivalences funext
open import globular-types.reflexive-globular-types funext
```

</details>

## Idea

Consider a family of
[reflexive globular types](globular-types.reflexive-globular-types.md)
`H : G₀ → Reflexive-Globular-Type` indexed by the 0-cells of a reflexive
globular type `G` and consider a
[dependent reflexive globular type](globular-types.dependent-reflexive-globular-types.md)
`K` over `G`. We say that `K` is a
{{#concept "pointwise extension" Disambiguation="family of reflexive globular types"}}
of `H` if it comes equipped with a family of
[reflexive globular equivalences](globular-types.reflexive-globular-equivalences.md)

```text
  ev-point K x ≃ H x₀
```

indexed by the [points](globular-types.points-reflexive-globular-types.md) of
`G`.

## Definitions

### The predicate of being a pointwise extension of a family of reflexive globular types

```agda
open import foundation.function-extensionality-axiom

module
  _
  (funext : function-extensionality)
  where
  {l1 l2 l3 l4 l5 l6 : Level} {G : Reflexive-Globular-Type l1 l2}
  (H : 0-cell-Reflexive-Globular-Type G → Reflexive-Globular-Type l3 l4)
  (K : Dependent-Reflexive-Globular-Type l5 l6 G)
  where

  is-pointwise-extension-family-of-reflexive-globular-types-Dependent-Reflexive-Globular-Type :
    UU (l1 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  is-pointwise-extension-family-of-reflexive-globular-types-Dependent-Reflexive-Globular-Type =
    (x : point-Reflexive-Globular-Type G) →
    reflexive-globular-equiv
      ( ev-point-Dependent-Reflexive-Globular-Type K x)
      ( H x)
```

### The type of pointwise extensions of a family of reflexive globular types

```agda
module _
  {l1 l2 l3 l4 : Level} (l5 l6 : Level) (G : Reflexive-Globular-Type l1 l2)
  (H : 0-cell-Reflexive-Globular-Type G → Reflexive-Globular-Type l3 l4)
  where

  pointwise-extension-family-of-reflexive-globular-types :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5 ⊔ lsuc l6)
  pointwise-extension-family-of-reflexive-globular-types =
    Σ ( Dependent-Reflexive-Globular-Type l5 l6 G)
      ( is-pointwise-extension-family-of-reflexive-globular-types-Dependent-Reflexive-Globular-Type
        H)
```
