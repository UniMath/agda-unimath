# Subuniverses

```agda
module foundation-core.subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.propositions
```

</details>

## Idea

**Subuniverses** are [subtypes](foundation-core.subtypes.md) of the universe.

## Definitions

### Subuniverses

```agda
is-subuniverse :
  {l1 l2 : Level} (P : UU l1 → UU l2) → UU (lsuc l1 ⊔ l2)
is-subuniverse P = (X : UU _) → is-prop (P X)

subuniverse :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
subuniverse l1 l2 = UU l1 → Prop l2

is-subtype-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  is-prop (type-Prop (P X))
is-subtype-subuniverse P X = is-prop-type-Prop (P X)

module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  where

  is-in-subuniverse : (X : UU l1) → UU l2
  is-in-subuniverse X = type-Prop (P X)

  is-prop-is-in-subuniverse : (X : UU l1) → is-prop (is-in-subuniverse X)
  is-prop-is-in-subuniverse X = is-prop-type-Prop (P X)

  type-subuniverse : UU (lsuc l1 ⊔ l2)
  type-subuniverse = Σ (UU l1) is-in-subuniverse

  inclusion-subuniverse : type-subuniverse → UU l1
  inclusion-subuniverse = pr1

  is-in-subuniverse-inclusion-subuniverse :
    (X : type-subuniverse) → is-in-subuniverse (inclusion-subuniverse X)
  is-in-subuniverse-inclusion-subuniverse = pr2
```
