# Localizations at maps

```agda
module orthogonal-factorization-systems.localizations-at-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.localizations-at-subuniverses
open import orthogonal-factorization-systems.types-local-at-maps
```

</details>

## Idea

Let `f` be a map of type `A → B` and let `X` be a type. The **localization** of
`X` at `f`, or **`f`-localization**, is an
`f`-[local](orthogonal-factorization-systems.types-local-at-maps.md) type `Y`
together with a map `η : X → Y` with the property that every type that is
`f`-local is also `η`-local.

## Definition

### The predicate of being a localization at a map

```agda
is-localization :
  {l1 l2 l3 l4 : Level} (l5 : Level)
  {A : UU l1} {B : UU l2} (f : A → B)
  (X : UU l3) (Y : UU l4) (η : X → Y) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5)
is-localization l5 f X Y η =
  ( is-local f Y) ×
  ( (Z : UU l5) → is-local f Z → is-local η Z)
```

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {f : A → B}
  {X : UU l3} {Y : UU l4} {η : X → Y}
  (is-localization-Y : is-localization l5 f X Y η)
  where

  is-local-is-localization : is-local f Y
  is-local-is-localization = pr1 is-localization-Y
```

### The type of localizations of a type with respect to a map

```agda
localization :
  {l1 l2 l3 : Level} (l4 l5 : Level)
  {A : UU l1} {B : UU l2} (f : A → B)
  (X : UU l3) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4 ⊔ lsuc l5)
localization l4 l5 f X =
  Σ (UU l4) (λ Y → Σ (X → Y) (is-localization l5 f X Y))
```

## Properties

### Localizations at a map are localizations at a subuniverse

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} (f : A → B)
  (X : UU l3) (Y : UU l4) (η : X → Y)
  where

  is-subuniverse-localization-is-localization :
    is-localization l4 f X Y η →
    is-subuniverse-localization (is-local-Prop f) X Y
  pr1 (is-subuniverse-localization-is-localization is-localization-Y) =
    pr1 is-localization-Y
  pr1 (pr2 (is-subuniverse-localization-is-localization is-localization-Y)) = η
  pr2 (pr2 (is-subuniverse-localization-is-localization is-localization-Y))
    (Z , is-local-Z) =
    pr2 is-localization-Y Z is-local-Z
```

It remains to construct a converse.

## References

{{#bibliography}} {{#reference RSS20}} {{#reference Rij19}}
