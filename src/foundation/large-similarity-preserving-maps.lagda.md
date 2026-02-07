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
    {l1 l2 : Level} {x₁ : X l1} {x₂ : X l2} →
    sim-Large-Similarity-Relation SX x₁ x₂ →
    sim-Large-Similarity-Relation SY (f x₁) (f x₂)

  reflects-sim-map-Large-Similarity-Relation : UUω
  reflects-sim-map-Large-Similarity-Relation =
    {l1 l2 : Level} {x₁ : X l1} {x₂ : X l2} →
    sim-Large-Similarity-Relation SY (f x₁) (f x₂) →
    sim-Large-Similarity-Relation SX x₁ x₂

  preserves-and-reflects-sim-map-Large-Similarity-Relation : UUω
  preserves-and-reflects-sim-map-Large-Similarity-Relation =
    {l1 l2 : Level} {x₁ : X l1} {x₂ : X l2} →
    ( sim-Large-Similarity-Relation SX x₁ x₂ ↔
      sim-Large-Similarity-Relation SY (f x₁) (f x₂))

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

## Properties

### Similarity-reflecting operations at a universe level are embeddings

```agda
module _
  {αX αY : Level → Level}
  {βX βY : Level → Level → Level}
  {X : (l : Level) → UU (αX l)}
  {Y : (l : Level) → UU (αY l)}
  (SX : Large-Similarity-Relation βX X)
  (SY : Large-Similarity-Relation βY Y)
  (f : {l : Level} → X l → Y l)
  (reflects-f : reflects-sim-map-Large-Similarity-Relation SX SY f)
  where

  abstract
    is-injective-reflects-sim-map-Large-Similarity-Relation :
      (l : Level) → is-injective (f {l})
    is-injective-reflects-sim-map-Large-Similarity-Relation
      l {x₁} {x₂} fx₁=fx₂ =
      eq-sim-Large-Similarity-Relation
        ( SX)
        ( x₁)
        ( x₂)
        ( reflects-f (sim-eq-Large-Similarity-Relation SY fx₁=fx₂))

    is-emb-reflects-sim-map-Large-Similarity-Relation :
      (l : Level) → is-emb (f {l})
    is-emb-reflects-sim-map-Large-Similarity-Relation l =
      is-emb-is-injective
        ( is-set-type-Large-Similarity-Relation SY l)
        ( is-injective-reflects-sim-map-Large-Similarity-Relation l)
```
