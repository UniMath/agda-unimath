# Large similarity preserving maps

```agda
module foundation.large-similarity-preserving-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-similarity-relations
open import foundation.injective-maps
open import foundation.large-binary-relations
open import foundation.universe-levels
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.embeddings
```

</details>

## Idea

## Definition

```agda
module _
  {αX αY : Level → Level}
  {βX βY : Level → Level → Level}
  {X : (l : Level) → UU (αX l)}
  {Y : (l : Level) → UU (αY l)}
  (SX : Large-Similarity-Relation βX X)
  (SY : Large-Similarity-Relation βY Y)
  {γ : Level → Level}
  (f : {l : Level} → X l → Y (γ l))
  where

  preserves-sim-map-Large-Similarity-Relation : UUω
  preserves-sim-map-Large-Similarity-Relation =
    {l1 l2 : Level} (x₁ : X l1) (x₂ : X l2) →
    sim-Large-Similarity-Relation SX x₁ x₂ →
    sim-Large-Similarity-Relation SY (f x₁) (f x₂)

record
  sim-preserving-map-Large-Similarity-Relation
    {αX αY : Level → Level}
    {βX βY : Level → Level → Level}
    {X : (l : Level) → UU (αX l)}
    {Y : (l : Level) → UU (αY l)}
    (SX : Large-Similarity-Relation βX X)
    (SY : Large-Similarity-Relation βY Y) :
    UUω
  where

  field
    map-sim-preserving-map-Large-Similarity-Relation :
      {l : Level} → X l → Y l
    preserves-sim-map-sim-preserving-map-Large-Similarity-Relation :
      preserves-sim-map-Large-Similarity-Relation
        ( SX)
        ( SY)
        ( map-sim-preserving-map-Large-Similarity-Relation)

open sim-preserving-map-Large-Similarity-Relation public
```
