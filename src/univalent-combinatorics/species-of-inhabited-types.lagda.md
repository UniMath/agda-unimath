#  Species of inhabited types

```agda
module univalent-combinatorics.species-of-inhabited-types where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.universe-levels

open import univalent-combinatorics.species-of-types
```

### Idea

In this file, we define the type of species of inhabited types. A species of inhabited types is just a map from an universe of inhabited types to an other universe.

## Definitions

### Species

```agda
species-inhabited-types : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
species-inhabited-types l1 l2 = Inhabited-Type l1 → UU l2
```

### Transport in species

```agda
tr-species-finite-types :
  {l1 l2 : Level} (F : species-inhabited-types l1 l2)
  (X Y : Inhabited-Type l1) →
  type-Inhabited-Type X ≃ type-Inhabited-Type Y → F X → F Y
tr-species-finite-types F X Y e = tr F (eq-equiv-Inhabited-Type X Y e)
```

### Extension into species of types

```agda
module _
  {l1 l2 : Level} (S : species-inhabited-types l1 l2)
  where

  Σ-extension-species-inhabited-types :
    species-types (l1) (l1 ⊔ l2)
  Σ-extension-species-inhabited-types X =
    Σ (is-inhabited X) (λ p → S (X , p))

  Π-extension-species-inhabited-types :
    species-types (l1) (l1 ⊔ l2)
  Π-extension-species-inhabited-types X =
    (p : is-inhabited X) → S (X , p)
```
