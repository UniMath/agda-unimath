# Smash products of pointed types

```agda
module synthetic-homotopy-theory.smash-products-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.constant-maps
open import foundation.equational-reasoning
open import foundation.function-extensionality
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.pointed-types
open import structured-types.pointed-maps
open import structured-types.pointed-cartesian-product-types

open import synthetic-homotopy-theory.cofibers
open import synthetic-homotopy-theory.wedges-of-pointed-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

Given two pointed types `a : A` and `b : B` we may form their **smash product**
as the following pushout

```md
 A ∨* B ----> A ×* B
    |           |
    |           |
    v        ⌜  v
  unit -----> A ∧* B
```

where the map `A ∨* B → A ×* B` is the canonical inclusion
`map-wedge-prod-Pointed-Type`.

## Definition

```agda
_∧*_ :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  Pointed-Type (l1 ⊔ l2)
pr1 (A ∧* B) =
  pushout
    ( map-prod-wedge-Pointed-Type A B)
    ( λ _ → star)
pr2 (A ∧* B) =
  inr-pushout
    ( map-prod-wedge-Pointed-Type A B)
    ( λ _ → star)
    ( star)
```

## Properties

### The pointed map from the product to the smash product

```agda
pointed-map-smash-prod-prod-Pointed-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  (A ×* B) →* (A ∧* B)
pr1 (pointed-map-smash-prod-prod-Pointed-Type A B) =
  inl-pushout (map-prod-wedge-Pointed-Type A B) (λ _ → star)
pr2 (pointed-map-smash-prod-prod-Pointed-Type A B) =
  ( ap
    ( inl-pushout
      ( map-prod-wedge-Pointed-Type A B)
      ( λ _ → star))
    ( inv
      ( preserves-point-pointed-map
        (A ∨* B)
        (A ×* B)
        ( pointed-map-prod-wedge-Pointed-Type A B)))) ∙
  ( glue-pushout
    ( map-prod-wedge-Pointed-Type A B)
    ( λ _ → star)
    ( point-Pointed-Type (A ∨* B)))
```

### The smash product is the product in the category of pointed types

```agda
map-gap-smash-prod-Pointed-Type :
  {l1 l2 l3 : Level}
  (A : Pointed-Type l1) (B : Pointed-Type l2) (S : Pointed-Type l3) →
  (f : S →* A) (g : S →* B) → type-Pointed-Type S → type-Pointed-Type (A ∧* B)
map-gap-smash-prod-Pointed-Type A B S f g s =
  inl-pushout
    ( map-prod-wedge-Pointed-Type A B)
    ( λ _ → star)
    ( map-pointed-map S A f s , map-pointed-map S B g s)

gap-smash-prod-Pointed-Type :
  {l1 l2 l3 : Level}
  (A : Pointed-Type l1) (B : Pointed-Type l2) (S : Pointed-Type l3) →
  (f : S →* A) (g : S →* B) → S →* (A ∧* B)
gap-smash-prod-Pointed-Type A B S f g =
  pointed-map-smash-prod-prod-Pointed-Type A B ∘*
  gap-prod-Pointed-Type A B S f g
```

It remains to show that this is the correct map, and that it is unique.

## See also

- [Wedges of pointed types](synthetic-homotopy-theory.wedges-of-pointed-types.md)
