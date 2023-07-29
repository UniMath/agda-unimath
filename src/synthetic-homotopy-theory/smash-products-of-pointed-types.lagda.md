# Smash products of pointed types

```agda
module synthetic-homotopy-theory.smash-products-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.pointed-cartesian-product-types
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.pointed-unit-type

open import synthetic-homotopy-theory.cocones-under-spans-of-pointed-types
open import synthetic-homotopy-theory.pushouts-of-pointed-types
open import synthetic-homotopy-theory.wedges-of-pointed-types
```

</details>

## Idea

Given two pointed types `a : A` and `b : B` we may form their **smash product**
as the following pushout

```text
 A ∨∗ B ----> A ×∗ B
    |           |
    |           |
    v        ⌜  v
  unit -----> A ∧∗ B
```

where the map `A ∨∗ B → A ×∗ B` is the canonical inclusion
`map-wedge-prod-Pointed-Type`.

## Definition

```agda
smash-prod-Pointed-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  Pointed-Type (l1 ⊔ l2)
smash-prod-Pointed-Type A B =
  pushout-Pointed-Type
    ( pointed-map-prod-wedge-Pointed-Type A B)
    ( terminal-pointed-map (A ∨∗ B))

_∧∗_ = smash-prod-Pointed-Type
```

**Note**: The symbols used for the smash product `_∧∗_` are the
[logical and](https://codepoints.net/U+2227) `∧` (agda-input: `\wedge` `\and`),
and the [asterisk operator](https://codepoints.net/U+2217) `∗` (agda-input:
`\ast`), not the [asterisk](https://codepoints.net/U+002A) `*`.

```agda
cogap-smash-prod-Pointed-Type :
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {X : Pointed-Type l3} →
  type-cocone-Pointed-Type
    ( pointed-map-prod-wedge-Pointed-Type A B)
    ( terminal-pointed-map (A ∨∗ B)) X →
  (A ∧∗ B) →∗ X
cogap-smash-prod-Pointed-Type {A = A} {B} =
  cogap-Pointed-Type
    ( pointed-map-prod-wedge-Pointed-Type A B)
    ( terminal-pointed-map (A ∨∗ B))

map-cogap-smash-prod-Pointed-Type :
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {X : Pointed-Type l3} →
  type-cocone-Pointed-Type
    ( pointed-map-prod-wedge-Pointed-Type A B)
    ( terminal-pointed-map (A ∨∗ B))
    ( X) →
  type-Pointed-Type (A ∧∗ B) → type-Pointed-Type X
map-cogap-smash-prod-Pointed-Type c =
  pr1 (cogap-smash-prod-Pointed-Type c)
```

## Properties

### The canonical pointed map from the product to the smash product

```agda
pointed-map-smash-prod-prod-Pointed-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  (A ×∗ B) →∗ (A ∧∗ B)
pointed-map-smash-prod-prod-Pointed-Type A B =
  inl-pushout-Pointed-Type
    ( pointed-map-prod-wedge-Pointed-Type A B)
    ( terminal-pointed-map (A ∨∗ B))
```

### The smash product is the product in the category of pointed types

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {S : Pointed-Type l3}
  where

  gap-smash-prod-Pointed-Type :
    (f : S →∗ A) (g : S →∗ B) → S →∗ (A ∧∗ B)
  gap-smash-prod-Pointed-Type f g =
    pointed-map-smash-prod-prod-Pointed-Type A B ∘∗
    gap-prod-Pointed-Type f g

  map-gap-smash-prod-Pointed-Type :
    (f : S →∗ A) (g : S →∗ B) → type-Pointed-Type S → type-Pointed-Type (A ∧∗ B)
  map-gap-smash-prod-Pointed-Type f g =
    pr1 (gap-smash-prod-Pointed-Type f g)
```

It remains to show that this is the correct map, and that it is unique.

## See also

- [Wedges of pointed types](synthetic-homotopy-theory.wedges-of-pointed-types.md)
