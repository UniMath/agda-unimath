# Structured equality duality

```agda
module foundation.structured-equality-duality where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.maps-in-subuniverses
open import foundation.separated-types-subuniverses
open import foundation.structure
open import foundation.subuniverses
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.families-of-equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.retractions
open import foundation-core.retracts-of-types
open import foundation-core.sections
open import foundation-core.torsorial-type-families
```

</details>

## Idea

Given a [structure](foundation.structure.md) `𝒫` on types that transfers along
[equivalences](foundation-core.equivalences.md), then for every type `A` and
type family `B : A → 𝒰` there is a
[mutual correspondence](foundation.logical-equivalences.md) between

1. For every `x : A`, `𝒫`-structured families of maps
   `f : (y : A) → (x ＝ y) → B y`.
2. `𝒫`-structures on the equality of `Σ A B`.

## Construction

```agda
module _
  {l1 l2 l3 : Level} {𝒫 : UU (l1 ⊔ l2) → UU l3}
  (tr-𝒫 : {X Y : UU (l1 ⊔ l2)} → X ≃ Y → 𝒫 X → 𝒫 Y)
  {A : UU l1} {B : A → UU l2}
  where

  forward-implication-structured-equality-duality :
    ( (x : A) (f : (y : A) → (x ＝ y) → B y) (y : A) → structure-map 𝒫 (f y)) →
    structure-equality 𝒫 (Σ A B)
  forward-implication-structured-equality-duality
    K (x , b) (x' , b') =
    tr-𝒫
      ( compute-fiber-map-out-of-identity-type (ind-Id x (λ u _ → B u) b) x' b')
      ( K x (ind-Id x (λ u _ → B u) b) x' b')

  backward-implication-structured-equality-duality :
    structure-equality 𝒫 (Σ A B) →
    ( (x : A) (f : (y : A) → (x ＝ y) → B y) (y : A) → structure-map 𝒫 (f y))
  backward-implication-structured-equality-duality K x f y b =
    tr-𝒫
      ( inv-compute-fiber-map-out-of-identity-type f y b)
      ( K (x , f x refl) (y , b))

  structured-equality-duality :
    ( (x : A) (f : (y : A) → (x ＝ y) → B y) (y : A) → structure-map 𝒫 (f y)) ↔
    ( structure-equality 𝒫 (Σ A B))
  structured-equality-duality =
    ( forward-implication-structured-equality-duality ,
      backward-implication-structured-equality-duality)
```

## Corollaries

### Subuniverse equality duality

Given a subuniverse `𝒫` then the following are logically equivalent:

1. For every `x : A`, every family of maps `f : (y : A) → (x ＝ y) → B y` is a
   family of `𝒫`-maps.
2. The dependent sum `Σ A B` is `𝒫`-separated.

```agda
module _
  {l1 l2 l3 : Level} (𝒫 : subuniverse (l1 ⊔ l2) l3)
  {A : UU l1} {B : A → UU l2}
  where

  abstract
    forward-implication-subuniverse-equality-duality :
      ( (x : A) (f : (y : A) → (x ＝ y) → B y)
        (y : A) → is-in-subuniverse-map 𝒫 (f y)) →
      is-separated 𝒫 (Σ A B)
    forward-implication-subuniverse-equality-duality =
      forward-implication-structured-equality-duality
        ( is-in-subuniverse-equiv 𝒫)

  abstract
    backward-implication-subuniverse-equality-duality :
      is-separated 𝒫 (Σ A B) →
      ( (x : A) (f : (y : A) → (x ＝ y) → B y)
        (y : A) → is-in-subuniverse-map 𝒫 (f y))
    backward-implication-subuniverse-equality-duality =
      backward-implication-structured-equality-duality
        ( is-in-subuniverse-equiv 𝒫)

  abstract
    subuniverse-equality-duality :
      ( (x : A) (f : (y : A) → (x ＝ y) → B y)
        (y : A) → is-in-subuniverse-map 𝒫 (f y)) ↔
      is-separated 𝒫 (Σ A B)
    subuniverse-equality-duality =
      structured-equality-duality (is-in-subuniverse-equiv 𝒫)
```
