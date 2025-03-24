# Fibers of pointed maps

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module structured-types.fibers-of-pointed-maps
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps funext
open import foundation.universe-levels

open import structured-types.pointed-maps funext univalence truncations
open import structured-types.pointed-types
```

</details>

## Definition

```agda
fiber-Pointed-Type :
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} →
  (A →∗ B) → Pointed-Type (l1 ⊔ l2)
pr1 (fiber-Pointed-Type f) = fiber (map-pointed-map f) (point-Pointed-Type _)
pr1 (pr2 (fiber-Pointed-Type f)) = point-Pointed-Type _
pr2 (pr2 (fiber-Pointed-Type f)) = preserves-point-pointed-map f
```
