#  General Species

```agda
module univalent-combinatorics.general-species where

open import foundation.equivalences
open import foundation.identity-types
open import foundation.univalence
open import foundation.universe-levels

```

### Idea

In this file, we define the type of general species. A general species is just a
map from an universe to another one.

## Definitions

### General-Species

```agda
general-species : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
general-species l1 l2 = UU l1 → UU l2
```

### Transport in species

```agda
tr-general-species :
  {l1 l2 : Level} (F : general-species l1 l2) (X Y : UU l1) →
  X ≃ Y → F X → F Y
tr-general-species F X Y e = tr F (eq-equiv X Y e)
```
