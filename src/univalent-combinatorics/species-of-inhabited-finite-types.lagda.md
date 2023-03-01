#  Species of inhabited finite types

```agda
module univalent-combinatorics.species-of-inhabited-finite-types where

open import foundation.equivalences
open import foundation.functions
open import foundation.identity-types
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
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
