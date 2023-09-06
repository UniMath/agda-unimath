# Suspensions of pointed types

```agda
module synthetic-homotopy-theory.suspensions-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.commuting-squares-of-maps
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-systems
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.transport
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import structured-types.pointed-equivalences
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-suspension-structures
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.dependent-universal-property-suspensions
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.suspensions-of-types
open import synthetic-homotopy-theory.universal-property-pushouts
open import synthetic-homotopy-theory.universal-property-suspensions
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
  const X (point-Pointed-Type Y ＝ point-Pointed-Type Y) refl
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
