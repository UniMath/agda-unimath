#  Species of finite types

```agda
module univalent-combinatorics.species-of-finite-types where

open import foundation.equivalences
open import foundation.functions
open import foundation.identity-types
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
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
