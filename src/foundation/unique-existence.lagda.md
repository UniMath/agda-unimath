# Unique existence

```agda
module foundation.unique-existence where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

Unique existence `∃! A B` is defined as `Σ A B` being contractible.

## Definition

```agda
∃! : {l1 l2 : Level} → (A : UU l1) → (A → UU l2) → UU (l1 ⊔ l2)
∃! A B = is-contr (Σ A B)
```
