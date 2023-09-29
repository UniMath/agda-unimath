# Propositions

```agda
module foundation.propositions where

open import foundation-core.propositions public
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.retractions
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Properties

### Propositions are `k+1`-truncated for any `k`

```agda
abstract
  is-trunc-is-prop :
    {l : Level} (k : 𝕋) {A : UU l} → is-prop A → is-trunc (succ-𝕋 k) A
  is-trunc-is-prop k is-prop-A x y = is-trunc-is-contr k (is-prop-A x y)

truncated-type-Prop : {l : Level} (k : 𝕋) → Prop l → Truncated-Type l (succ-𝕋 k)
pr1 (truncated-type-Prop k P) = type-Prop P
pr2 (truncated-type-Prop k P) = is-trunc-is-prop k (is-prop-type-Prop P)
```

### Propositions are closed under retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : UU l2)
  where

  is-prop-retract-of : A retract-of B → is-prop B → is-prop A
  is-prop-retract-of = is-trunc-retract-of
```
