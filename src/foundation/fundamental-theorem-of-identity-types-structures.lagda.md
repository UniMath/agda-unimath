# The fundamental theorem of identity types for structures

```agda
module foundation.fundamental-theorem-of-identity-types-structures where
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

> TODO

## Theorem

### The unbased fundamental theorem of identity types for structures

Given a structure `𝒫` on types that transports along equivalences, then the
following are logically equivalent:

1. For every `x : A`, every family of maps map out of the identity types of `A`,
   `f : (y : A) → (x ＝ y) → B y` is `𝒫`-structured.
2. The identity types of `Σ A B` are `𝒫`-structured.

```agda
module _
  {l1 l2 l3 : Level} {𝒫 : UU (l1 ⊔ l2) → UU l3}
  (tr-𝒫 : {X Y : UU (l1 ⊔ l2)} → X ≃ Y → 𝒫 X → 𝒫 Y)
  {A : UU l1} {B : A → UU l2}
  where

  forward-implication-fundamental-theorem-unbased-id-structure :
    ( (x : A) (f : (y : A) → (x ＝ y) → B y) (y : A) → structure-map 𝒫 (f y)) →
    structure-equality 𝒫 (Σ A B)
  forward-implication-fundamental-theorem-unbased-id-structure
    K (x , b) (x' , b') =
    tr-𝒫
      ( compute-fiber-map-out-of-identity-type (ind-Id x (λ u _ → B u) b) x' b')
      ( K x (ind-Id x (λ u _ → B u) b) x' b')

  backward-implication-fundamental-theorem-unbased-id-structure :
    structure-equality 𝒫 (Σ A B) →
    ( (x : A) (f : (y : A) → (x ＝ y) → B y) (y : A) → structure-map 𝒫 (f y))
  backward-implication-fundamental-theorem-unbased-id-structure K x f y b =
    tr-𝒫
      ( inv-compute-fiber-map-out-of-identity-type f y b)
      ( K (x , f x refl) (y , b))

  fundamental-theorem-unbased-id-structure :
    ( (x : A) (f : (y : A) → (x ＝ y) → B y) (y : A) → structure-map 𝒫 (f y)) ↔
    ( structure-equality 𝒫 (Σ A B))
  fundamental-theorem-unbased-id-structure =
    ( forward-implication-fundamental-theorem-unbased-id-structure ,
      backward-implication-fundamental-theorem-unbased-id-structure)
```

### The unbased fundamental theorem of identity types for subuniverses

Given a subuniverse `𝒫` then the following are logically equivalent:

1. Every unbased map out of the identity types of `A` into the type family
   `B : A → 𝒰` is in `𝒫`.
2. The dependent sum `Σ A B` is `𝒫`-separated.

```agda
module _
  {l1 l2 l3 : Level} (𝒫 : subuniverse (l1 ⊔ l2) l3)
  {A : UU l1} {B : A → UU l2}
  where

  abstract
    forward-implication-fundamental-theorem-unbased-id-subuniverse :
      ( (x : A) (f : (y : A) → (x ＝ y) → B y)
        (y : A) → is-in-subuniverse-map 𝒫 (f y)) →
      is-separated 𝒫 (Σ A B)
    forward-implication-fundamental-theorem-unbased-id-subuniverse =
      forward-implication-fundamental-theorem-unbased-id-structure
        ( is-in-subuniverse-equiv 𝒫)

  abstract
    backward-implication-fundamental-theorem-unbased-id-subuniverse :
      is-separated 𝒫 (Σ A B) →
      ( (x : A) (f : (y : A) → (x ＝ y) → B y)
        (y : A) → is-in-subuniverse-map 𝒫 (f y))
    backward-implication-fundamental-theorem-unbased-id-subuniverse =
      backward-implication-fundamental-theorem-unbased-id-structure
        ( is-in-subuniverse-equiv 𝒫)

  abstract
    fundamental-theorem-unbased-id-subuniverse :
      ( (x : A) (f : (y : A) → (x ＝ y) → B y)
        (y : A) → is-in-subuniverse-map 𝒫 (f y)) ↔
      is-separated 𝒫 (Σ A B)
    fundamental-theorem-unbased-id-subuniverse =
      fundamental-theorem-unbased-id-structure (is-in-subuniverse-equiv 𝒫)
```
