# Torsorial type families

```agda
module foundation-core.torsorial-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-types
```

</details>

## Idea

A type family `B` over `A` is said to be **torsorial** if its
[total space](foundation.dependent-pair-types.md) is
[contractible](foundation-core.contractible-types.md).

## Definition

### The predicate of being a torsorial type family

```agda
is-torsorial :
  {l1 l2 : Level} {B : UU l1} → (B → UU l2) → UU (l1 ⊔ l2)
is-torsorial E = is-contr (Σ _ E)
```
