# Torsorial type families

```agda
module foundation.torsorial-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A type family `E` over `B` is said to be **torsorial** if its [total space](foundation.dependent-pair-types.md) is [contractible](foundation.contractible-types.md). By the [fundamental theorem of identity types](foundation.fundamental-theorem-of-identity-types.md) it follows that a type family `E` is torsorial if and only if it is in the [image](foundation.images.md) of `Id : B → (B → 𝒰)`.

## Definition

### The predicate of being a torsorial type family over `B`

```agda
is-torsorial-Prop :
  {l1 l2 : Level} {B : UU l1} → (B → UU l2) → Prop (l1 ⊔ l2)
is-torsorial-Prop E = is-contr-Prop (Σ _ E)

is-torsorial :
  {l1 l2 : Level} {B : UU l1} → (B → UU l2) → UU (l1 ⊔ l2)
is-torsorial E = type-Prop (is-torsorial-Prop E)

is-prop-is-torsorial :
  {l1 l2 : Level} {B : UU l1} (E : B → UU l2) → is-prop (is-torsorial E)
is-prop-is-torsorial E = is-prop-type-Prop (is-torsorial-Prop E)
```

### The type of torsorial type families over `B`

```agda
torsorial-family-of-types :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
torsorial-family-of-types l2 B = Σ (B → UU l2) is-torsorial

module _
  {l1 l2 : Level} {B : UU l1} (T : torsorial-family-of-types l2 B)
  where
  
  type-torsorial-family-of-types : B → UU l2
  type-torsorial-family-of-types = pr1 T

  is-torsorial-torsorial-family-of-types :
    is-torsorial type-torsorial-family-of-types
  is-torsorial-torsorial-family-of-types = pr2 T
```
