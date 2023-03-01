#  Species of inhabited finite types

```agda
module univalent-combinatorics.species-of-inhabited-finite-types where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.universe-levels

open import univalent-combinatorics.dependent-sum-finite-types
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
open import univalent-combinatorics.species-of-finite-types
open import univalent-combinatorics.species-of-inhabited-types
open import univalent-combinatorics.species-of-types
```

### Idea

In this file, we define the type of species of inhabited finite types. A species of inhabited finite types is just a map from a universe of inhabited finite types to 𝔽.

## Definitions

### Species

```agda
species-inhabited-finite-types : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
species-inhabited-finite-types l1 l2 = Inhabited-Type-𝔽 l1 → 𝔽 l2
```

### Transport in species

```agda
tr-species-inhabited-finite-types :
  {l1 l2 : Level} (F : species-inhabited-finite-types l1 l2)
  (X Y : Inhabited-Type-𝔽 l1) →
  type-Inhabited-Type-𝔽 X ≃ type-Inhabited-Type-𝔽 Y → type-𝔽 (F X) → type-𝔽 (F Y)
tr-species-inhabited-finite-types F X Y e =
  tr (type-𝔽 ∘ F) (eq-equiv-Inhabited-Type-𝔽 X Y e)
```

### Extension into species of types

```agda
module _
  {l1 l2 : Level} (S : species-inhabited-finite-types l1 l2)
  where

  Σ-extension-inhabited-species-inhabited-finite-types :
    species-inhabited-types (l1) (l1 ⊔ l2)
  Σ-extension-inhabited-species-inhabited-finite-types X =
    Σ ( is-finite (type-Inhabited-Type X))
      ( λ p →
        type-𝔽
          ( S ((type-Inhabited-Type X , p), is-inhabited-type-Inhabited-Type X)))

  Π-extension-inhabited-species-inhabited-finite-types :
    species-inhabited-types (l1) (l1 ⊔ l2)
  Π-extension-inhabited-species-inhabited-finite-types X =
    ( p : is-finite (type-Inhabited-Type X)) →
    ( type-𝔽
        ( S ((type-Inhabited-Type X , p), is-inhabited-type-Inhabited-Type X)))

{-
  Σ-extension-finite-species-inhabited-finite-types :
    species-finite-types (l1) (l1 ⊔ l2)
  Σ-extension-finite-species-inhabited-finite-types X =
    Σ-𝔽 (is-inhabited (type-𝔽 X), {!!}) ( λ p → S (X , p))

  Π-extension-finite-species-inhabited-finite-types :
    species-finite-types (l1) (l1 ⊔ l2)
  Π-extension-finite-species-inhabited-finite-types X =
    Π-𝔽 (is-inhabited (type-𝔽 X), {!!}) (λ p → S (X , p))
-}

  Σ-extension-species-inhabited-finite-types :
    species-types (l1) (l1 ⊔ l2)
  Σ-extension-species-inhabited-finite-types X =
    Σ (is-inhabited X) (λ p → Σ (is-finite X) (λ f → type-𝔽 (S ((X , f ), p))))

  Π-extension-species-inhabited-finite-types :
    species-types (l1) (l1 ⊔ l2)
  Π-extension-species-inhabited-finite-types X =
    (p : is-inhabited X) → (f : is-finite X) → type-𝔽 (S ((X , f) , p))
```
