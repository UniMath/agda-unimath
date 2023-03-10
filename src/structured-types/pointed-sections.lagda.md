# Pointed sections of pointed maps

```agda
module structured-types.pointed-sections where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

A **pointed section** of a pointed map `f : A →* B` consists of a pointed map `g : B →* A` equipped with a pointed homotopy `H : (f ∘* g) ~* id`.

```agda
pointed-section-Pointed-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  (A →* B) → UU (l1 ⊔ l2)
pointed-section-Pointed-Type A B f =
  Σ ( B →* A)
    ( λ g → htpy-pointed-map B B (comp-pointed-map B A B f g) id-pointed-map)
```
