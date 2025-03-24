# Suspensions of pointed types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module synthetic-homotopy-theory.suspensions-of-pointed-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces funext univalence truncations
open import synthetic-homotopy-theory.suspension-structures funext univalence truncations
open import synthetic-homotopy-theory.suspensions-of-types funext univalence truncations
```

</details>

## Idea

When `X` is a pointed type, the suspension of `X` has nice properties

### The suspension of a pointed type

```agda
suspension-Pointed-Type :
  {l : Level} → Pointed-Type l → Pointed-Type l
pr1 (suspension-Pointed-Type X) = suspension (type-Pointed-Type X)
pr2 (suspension-Pointed-Type X) = north-suspension
```

#### Suspension structure induced by a pointed type

```agda
constant-suspension-structure-Pointed-Type :
  {l1 l2 : Level} (X : UU l1) (Y : Pointed-Type l2) →
  suspension-structure X (type-Pointed-Type Y)
pr1 (constant-suspension-structure-Pointed-Type X Y) =
  point-Pointed-Type Y
pr1 (pr2 (constant-suspension-structure-Pointed-Type X Y)) =
  point-Pointed-Type Y
pr2 (pr2 (constant-suspension-structure-Pointed-Type X Y)) =
  const X refl
```

#### Suspension structure induced by a map into a loop space

The following function takes a map `X → Ω Y` and returns a suspension structure
on `Y`.

```agda
module _
  {l1 l2 : Level} (X : UU l1) (Y : Pointed-Type l2)
  where
  suspension-structure-map-into-Ω :
    (X → type-Ω Y) → suspension-structure X (type-Pointed-Type Y)
  pr1 (suspension-structure-map-into-Ω f) = point-Pointed-Type Y
  pr1 (pr2 (suspension-structure-map-into-Ω f)) = point-Pointed-Type Y
  pr2 (pr2 (suspension-structure-map-into-Ω f)) = f
```
