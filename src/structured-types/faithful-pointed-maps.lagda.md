# Faithful pointed maps

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module structured-types.faithful-pointed-maps
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.faithful-maps funext
open import foundation.identity-types funext
open import foundation.universe-levels

open import structured-types.pointed-maps funext univalence truncations
open import structured-types.pointed-types
```

</details>

## Idea

A faithful pointed map from `A` to `B` is a pointed map from `A` to `B` of which
the underlying map is faithful.

## Definition

```agda
faithful-pointed-map :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) → UU (l1 ⊔ l2)
faithful-pointed-map A B =
  Σ (A →∗ B) (λ f → is-faithful (map-pointed-map f))

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (f : faithful-pointed-map A B)
  where

  pointed-map-faithful-pointed-map : A →∗ B
  pointed-map-faithful-pointed-map = pr1 f

  map-faithful-pointed-map : type-Pointed-Type A → type-Pointed-Type B
  map-faithful-pointed-map =
    map-pointed-map pointed-map-faithful-pointed-map

  preserves-point-faithful-pointed-map :
    map-faithful-pointed-map (point-Pointed-Type A) ＝ point-Pointed-Type B
  preserves-point-faithful-pointed-map =
    preserves-point-pointed-map pointed-map-faithful-pointed-map

  is-faithful-faithful-pointed-map : is-faithful map-faithful-pointed-map
  is-faithful-faithful-pointed-map = pr2 f
```
