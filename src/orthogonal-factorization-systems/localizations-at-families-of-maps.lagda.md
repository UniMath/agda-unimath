# Localizations at families of maps

```agda
module orthogonal-factorization-systems.localizations-at-families-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.universe-levels

open import orthogonal-factorization-systems.localizations-at-subuniverses
open import orthogonal-factorization-systems.types-local-at-maps
```

</details>

## Idea

Consider a family `F : (a : A) → (B a) → (C a)` of maps and let `X` be a type.
The **localization** of `X` at `F`, or **`F`-localization**, is a `F`-local type
`Y` (which means
`F a`-[local](orthogonal-factorization-systems.types-local-at-maps.md) for each
`a : A`) together with a map `η : X → Y` with the property that every type that
is `F`-local is also `η`-local.

## Definition

### The predicate of being a localization at a family of maps

```agda
is-localization-at-family :
  {l1 l2 l3 l4 l5 : Level} (l6 : Level)
  (A : UU l1) {B : A → UU l2} {C : A → UU l3}
  (F : (a : A) → (B a) → (C a))
  (X : UU l4) (Y : UU l5) (η : X → Y) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ lsuc l6)
is-localization-at-family l6 A F X Y η =
  ((a : A) → (is-local (F a) Y)) ×
  ( (Z : UU l6) → ((a : A) → ( is-local (F a) Z)) → is-local η Z)
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : UU l1) {B : A → UU l2} {C : A → UU l3}
  {F : (a : A) → (B a) → (C a)}
  {X : UU l4} {Y : UU l5} {η : X → Y}
  (is-localization-at-family-Y : is-localization-at-family l6 A F X Y η)
  where

  is-local-is-localization-at-family : (a : A) → (is-local (F a) Y)
  is-local-is-localization-at-family = pr1 is-localization-at-family-Y
```

### The type of localizations of a type with respect to a family of maps

```agda
localization-at-family :
  {l1 l2 l3 l4 : Level} (l5 l6 : Level)
  (A : UU l1) {B : A → UU l2} {C : A → UU l3}
  (F : (a : A) → (B a) → (C a))
  (X : UU l4) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5 ⊔ lsuc l6)
localization-at-family l5 l6 A F X =
  Σ (UU l5) (λ Y → Σ (X → Y) (is-localization-at-family l6 A F X Y))
```

## Properties

### Localizations at a family of maps are localizations at a subuniverse

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (A : UU l1) {B : A → UU l2} {C : A → UU l3} (F : (a : A) → (B a) → (C a))
  (X : UU l4) (Y : UU l5) (η : X → Y)
  where

  is-subuniverse-localization-is-localization-at-family :
    is-localization-at-family l5 A F X Y η →
    is-subuniverse-localization
      (λ W → (Π-Prop A (λ a → (is-local-Prop (F a) W)))) X Y
  pr1 (is-subuniverse-localization-is-localization-at-family
    is-localization-Y) =
    pr1 is-localization-Y
  pr1 (pr2 (is-subuniverse-localization-is-localization-at-family
    is-localization-Y)) =
    η
  pr2 (pr2 (is-subuniverse-localization-is-localization-at-family
    is-localization-Y))
    (Z , is-local-Z) =
    pr2 is-localization-Y Z is-local-Z
```

It remains to construct a converse.

## References

{{#bibliography}} {{#reference RSS20}} {{#reference Rij19}}
