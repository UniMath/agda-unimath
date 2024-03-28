# Suspensions of pointed types

```agda
module synthetic-homotopy-theory.suspensions-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.suspensions-of-types
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
