# Species of types

```agda
module species.species-of-types where
<<<<<<< HEAD

=======
```

<details><summary>Imports</summary>

```agda
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
open import foundation.equivalences
open import foundation.identity-types
open import foundation.univalence
open import foundation.universe-levels
```

<<<<<<< HEAD
=======
</details>

>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
### Idea

In this file, we define the type of species of types. A species of types is just
a map from an universe to another one.

## Definitions

### Species of types

```agda
species-types : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
species-types l1 l2 = UU l1 → UU l2
```

### Transport in species

```agda
tr-species-types :
  {l1 l2 : Level} (F : species-types l1 l2) (X Y : UU l1) →
  X ≃ Y → F X → F Y
tr-species-types F X Y e = tr F (eq-equiv X Y e)
```
