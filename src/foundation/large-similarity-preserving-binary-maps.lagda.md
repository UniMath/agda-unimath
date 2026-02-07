# Large similarity preserving binary maps

```agda
module foundation.large-similarity-preserving-binary-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-similarity-relations
open import foundation.injective-maps
open import foundation.large-binary-relations
open import foundation.universe-levels
open import foundation.large-similarity-preserving-maps
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.embeddings
```

</details>

## Idea

## Definition

```agda
module _
  {αX αY αZ : Level → Level}
  {βX βY βZ : Level → Level → Level}
  {X : (l : Level) → UU (αX l)}
  {Y : (l : Level) → UU (αY l)}
  {Z : (l : Level) → UU (αZ l)}
  (SX : Large-Similarity-Relation βX X)
  (SY : Large-Similarity-Relation βY Y)
  (SZ : Large-Similarity-Relation βZ Z)
  (f : {l1 l2 : Level} → X l1 → Y l2 → Z (l1 ⊔ l2))
  where

  preserves-sim-binary-map-Large-Similarity-Relation : UUω
  preserves-sim-binary-map-Large-Similarity-Relation =
    {l1 l2 l3 l4 : Level} {x₁ : X l1} {x₂ : X l2} {y₁ : Y l3} {y₂ : Y l4} →
    sim-Large-Similarity-Relation SX x₁ x₂ →
    sim-Large-Similarity-Relation SY y₁ y₂ →
    sim-Large-Similarity-Relation SZ (f x₁ y₁) (f x₂ y₂)

record
  sim-preserving-binary-map-Large-Similarity-Relation
    {αX αY αZ : Level → Level}
    {βX βY βZ : Level → Level → Level}
    {X : (l : Level) → UU (αX l)}
    {Y : (l : Level) → UU (αY l)}
    {Z : (l : Level) → UU (αZ l)}
    (SX : Large-Similarity-Relation βX X)
    (SY : Large-Similarity-Relation βY Y)
    (SZ : Large-Similarity-Relation βZ Z) :
    UUω
  where

  field
    map-sim-preserving-binary-map-Large-Similarity-Relation :
      {l1 l2 : Level} → X l1 → Y l2 → Z (l1 ⊔ l2)

    preserves-sim-map-sim-preserving-binary-map-Large-Similarity-Relation :
      preserves-sim-binary-map-Large-Similarity-Relation
        ( SX)
        ( SY)
        ( SZ)
        ( map-sim-preserving-binary-map-Large-Similarity-Relation)

open sim-preserving-binary-map-Large-Similarity-Relation public
```

## Properties

### A binary map preserves similarity if and only if it preserves similarity in each argument

```agda
module _
  {αX αY αZ : Level → Level}
  {βX βY βZ : Level → Level → Level}
  {X : (l : Level) → UU (αX l)}
  {Y : (l : Level) → UU (αY l)}
  {Z : (l : Level) → UU (αZ l)}
  (SX : Large-Similarity-Relation βX X)
  (SY : Large-Similarity-Relation βY Y)
  (SZ : Large-Similarity-Relation βZ Z)
  (f : {l1 l2 : Level} → X l1 → Y l2 → Z (l1 ⊔ l2))
  where

  abstract
    preserves-sim-left-preserves-sim-binary-map-Large-Similarity-Relation :
      preserves-sim-binary-map-Large-Similarity-Relation SX SY SZ f →
      {l : Level} (y : Y l) →
      preserves-sim-map-Large-Similarity-Relation SX SZ (λ x → f x y)
    preserves-sim-left-preserves-sim-binary-map-Large-Similarity-Relation
      H y x₁~x₂ =
      H x₁~x₂ (refl-sim-Large-Similarity-Relation SY y)

    preserves-sim-right-preserves-sim-binary-map-Large-Similarity-Relation :
      preserves-sim-binary-map-Large-Similarity-Relation SX SY SZ f →
      {l : Level} (x : X l) →
      preserves-sim-map-Large-Similarity-Relation SY SZ (λ y → f x y)
    preserves-sim-right-preserves-sim-binary-map-Large-Similarity-Relation
      H x =
      H (refl-sim-Large-Similarity-Relation SX x)

    preserves-sim-preserves-sim-left-right-binary-map-Large-Similarity-Relation :
      ( {l : Level} (y : Y l) →
        preserves-sim-map-Large-Similarity-Relation SX SZ (λ x → f x y)) →
      ( {l : Level} (x : X l) →
        preserves-sim-map-Large-Similarity-Relation SY SZ (λ y → f x y)) →
      preserves-sim-binary-map-Large-Similarity-Relation SX SY SZ f
    preserves-sim-preserves-sim-left-right-binary-map-Large-Similarity-Relation
      HX HY {x₁ = x₁} {x₂ = x₂} {y₁ = y₁} {y₂ = y₂} x₁~x₂ y₁~y₂ =
      transitive-sim-Large-Similarity-Relation SZ
        ( f x₁ y₁)
        ( f x₂ y₁)
        ( f x₂ y₂)
        ( HY x₂ y₁~y₂)
        ( HX y₁ x₁~x₂)
```
