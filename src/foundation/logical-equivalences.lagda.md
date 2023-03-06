# Logical equivalences

<details><summary>Imports</summary>
```agda
module foundation.logical-equivalences where
open import foundation-core.logical-equivalences public
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.identity-types
open import foundation-core.universe-levels
open import foundation.propositions
```
</details>

## Properties

### Two equal propositions are logically equivalent

```agda
iff-eq :
  {l1 : Level} {P Q : Prop l1} → P ＝ Q → P ⇔ Q
pr1 (iff-eq refl) = id
pr2 (iff-eq refl) = id
```

### The type of logical equivalences between propositions is a proposition

```agda
abstract
  is-prop-iff :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) → is-prop (P ⇔ Q)
  is-prop-iff P Q =
    is-prop-prod
      ( is-prop-function-type (is-prop-type-Prop Q))
      ( is-prop-function-type (is-prop-type-Prop P))
```

### Logical equivalence of propositions is equivalent to equivalence of propositions

```agda
abstract
  is-equiv-equiv-iff :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
    is-equiv (equiv-iff' P Q)
  is-equiv-equiv-iff P Q =
    is-equiv-is-prop
      ( is-prop-iff P Q)
      ( is-prop-type-equiv-Prop P Q)
      ( iff-equiv)

equiv-equiv-iff :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  (P ⇔ Q) ≃ (type-Prop P ≃ type-Prop Q)
pr1 (equiv-equiv-iff P Q) = equiv-iff' P Q
pr2 (equiv-equiv-iff P Q) = is-equiv-equiv-iff P Q
```

### The type of logical equivalences between propositions is a proposition

```agda
is-prop-logical-equivalence :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) → is-prop (P ⇔ Q)
is-prop-logical-equivalence P Q =
  is-prop-prod
    ( is-prop-function-type (is-prop-type-Prop Q))
    ( is-prop-function-type (is-prop-type-Prop P))
```
