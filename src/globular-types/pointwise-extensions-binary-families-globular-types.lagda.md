# Pointwise extensions of binary families of globular types

```agda
{-# OPTIONS --guardedness #-}

module
  globular-types.pointwise-extensions-binary-families-globular-types
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import globular-types.binary-dependent-globular-types funext
open import globular-types.globular-equivalences funext
open import globular-types.globular-types
open import globular-types.points-globular-types funext
```

</details>

## Idea

Consider two [globular types](globular-types.globular-types.md) `G` and `H`, and
a binary family

```text
  K : G₀ → H₀ → Globular-Type
```

of globular types, indexed over the 0-cells of `G` and `H`. Furthermore,
consider a
[binary dependent globular type](globular-types.binary-dependent-globular-types.md)
`L` over `G` and `H`. We say that `L` is a
{{#concept "pointwise extension" Disambiguation="binary family of globular types" Agda=is-pointwise-extension-binary-family-globular-types}}
of `K` if it comes equipped with a family of
[globular equivalences](globular-types.globular-equivalences.md)

```text
  (x : point G) (y : point H) → ev-point L x y ≃ K x₀ y₀.
```

## Definitions

### The predicate of being a pointwise extension of a binary family of globular types

```agda
open import foundation.function-extensionality-axiom

module _
  (funext : function-extensionality)
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {G : Globular-Type l1 l2} {H : Globular-Type l3 l4}
  (K : 0-cell-Globular-Type G → 0-cell-Globular-Type H → Globular-Type l5 l6)
  (L : Binary-Dependent-Globular-Type l7 l8 G H)
  where

  is-pointwise-extension-binary-family-globular-types :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8)
  is-pointwise-extension-binary-family-globular-types =
    (x : point-Globular-Type G) (y : point-Globular-Type H) →
    globular-equiv
      ( ev-point-Binary-Dependent-Globular-Type L x y)
      ( K (0-cell-point-Globular-Type x) (0-cell-point-Globular-Type y))
```

### The type of pointwise extensions of a binary family of globular types

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (l7 l8 : Level)
  {G : Globular-Type l1 l2} {H : Globular-Type l3 l4}
  (K : 0-cell-Globular-Type G → 0-cell-Globular-Type H → Globular-Type l5 l6)
  where

  pointwise-extension-binary-family-globular-types :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ lsuc l7 ⊔ lsuc l8)
  pointwise-extension-binary-family-globular-types =
    Σ ( Binary-Dependent-Globular-Type l7 l8 G H)
      ( is-pointwise-extension-binary-family-globular-types K)
```
