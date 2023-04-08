# Cauchy series of species of types in a subuniverse

```agda
module species.cauchy-series-species-of-types-in-subuniverse where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.subuniverses
open import foundation.universe-levels

open import species.cauchy-series-species-of-types
open import species.species-of-types-in-subuniverse
```

</details>

## Idea

The Cauchy series of a species `S` of types in subuniverse from `P` to `Q` at
`X` is defined as :

```md
Σ (U : type-subuniverse P) (S(U) × (U → X))
```

## Definition

```agda
cauchy-series-species-subuniverse :
  {l1 l2 l3 l4 : Level} (l5 : Level) → (P : subuniverse l1 l2) →
  (Q : subuniverse l3 l4) →  species-subuniverse P Q → UU l5 →
  UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l5)
cauchy-series-species-subuniverse {l1} l5 P Q S X =
  Σ ( type-subuniverse P)
    ( λ U → inclusion-subuniverse Q (S U) × (inclusion-subuniverse P U → X))
```
