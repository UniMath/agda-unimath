# Bands

```agda
module foundation.bands where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.set-truncations
open import foundation.universe-levels
```

</details>

## Idea

A band from $X$ to $Y$ is an element of the set-truncation of the type of equivalences from $X$ to $Y$.

## Definition

```agda
band : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
band A B = type-trunc-Set (A ≃ B)

unit-band : {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A ≃ B) → band A B
unit-band = unit-trunc-Set

refl-band : {l : Level} (A : UU l) → band A A
refl-band A = unit-band id-equiv
```
