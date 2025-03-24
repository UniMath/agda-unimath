# Pointwise extensions of binary families of reflexive globular types

```agda
{-# OPTIONS --guardedness #-}

module
  globular-types.pointwise-extensions-binary-families-reflexive-globular-types
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import globular-types.binary-dependent-reflexive-globular-types funext univalence truncations
open import globular-types.points-reflexive-globular-types funext univalence truncations
open import globular-types.reflexive-globular-equivalences funext univalence truncations
open import globular-types.reflexive-globular-types funext univalence truncations
```

</details>

## Idea

Consider two
[reflexive globular types](globular-types.reflexive-globular-types.md) `G` and
`H`, and a binary family

```text
  K : G₀ → H₀ → Reflexive-Globular-Type
```

of reflexive globular types, indexed over the 0-cells of `G` and `H`.
Furthermore, consider a
[binary dependent reflexive globular type](globular-types.binary-dependent-reflexive-globular-types.md)
`L` over `G` and `H`. We say that `L` is a
{{#concept "pointwise extension" Disambiguation="binary family of reflexive globular types" Agda=is-pointwise-extension-binary-family-reflexive-globular-types}}
of `K` if it comes equipped with a family of
[reflexive globular equivalences](globular-types.reflexive-globular-equivalences.md)

```text
  (x : point G) (y : point H) → ev-point L x y ≃ K x₀ y₀.
```

## Definitions

### The predicate of being a pointwise extension of a binary family of reflexive globular types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module _
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {G : Reflexive-Globular-Type l1 l2} {H : Reflexive-Globular-Type l3 l4}
  (K :
    0-cell-Reflexive-Globular-Type G →
    0-cell-Reflexive-Globular-Type H → Reflexive-Globular-Type l5 l6)
  (L : Binary-Dependent-Reflexive-Globular-Type l7 l8 G H)
  where

  is-pointwise-extension-binary-family-reflexive-globular-types :
    UU (l1 ⊔ l3 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8)
  is-pointwise-extension-binary-family-reflexive-globular-types =
    (x : point-Reflexive-Globular-Type G)
    (y : point-Reflexive-Globular-Type H) →
    reflexive-globular-equiv
      ( ev-point-Binary-Dependent-Reflexive-Globular-Type G H L x y)
      ( K x y)
```

### The type of pointwise extensions of a binary family of reflexive globular types

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (l7 l8 : Level)
  (G : Reflexive-Globular-Type l1 l2) (H : Reflexive-Globular-Type l3 l4)
  (K :
    0-cell-Reflexive-Globular-Type G →
    0-cell-Reflexive-Globular-Type H → Reflexive-Globular-Type l5 l6)
  where

  pointwise-extension-binary-family-reflexive-globular-types :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ lsuc l7 ⊔ lsuc l8)
  pointwise-extension-binary-family-reflexive-globular-types =
    Σ ( Binary-Dependent-Reflexive-Globular-Type l7 l8 G H)
      ( is-pointwise-extension-binary-family-reflexive-globular-types K)
```
