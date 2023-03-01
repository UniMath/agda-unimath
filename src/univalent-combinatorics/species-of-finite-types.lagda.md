#  Species of finite types

```agda
module univalent-combinatorics.species-of-finite-types where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.identity-types
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.species-of-types
```

### Idea

In this file, we define the type of species of finite types. A species of finite types is just a map from 𝔽 to a 𝔽.

## Definitions

### Species

```agda
species-finite-types : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
species-finite-types l1 l2 = 𝔽 l1 → 𝔽 l2
```

### Transport in species

```agda
tr-species-finite-types :
  {l1 l2 : Level} (F : species-finite-types l1 l2) (X Y : 𝔽 l1) →
  type-𝔽 X ≃ type-𝔽 Y → type-𝔽 (F X) → type-𝔽 (F Y)
tr-species-finite-types F X Y e = tr (type-𝔽 ∘ F) (eq-equiv-𝔽 X Y e)
```

### Extension into species of types

```agda
module _
  {l1 l2 : Level} (S : species-finite-types l1 l2)
  where

  Σ-extension-species-finite-types :
    species-types (l1) (l1 ⊔ l2)
  Σ-extension-species-finite-types X =
    Σ (is-finite X) (λ p → type-𝔽 (S (X , p)))

  Π-extension-species-finite-types :
    species-types (l1) (l1 ⊔ l2)
  Π-extension-species-finite-types X =
    (p : is-finite X) → type-𝔽 (S (X , p))
```
