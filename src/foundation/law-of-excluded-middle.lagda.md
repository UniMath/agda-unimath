# The law of excluded middle

```agda
module foundation.law-of-excluded-middle where

open import foundation-core.law-of-excluded-middle public
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.decidable-propositions
open import foundation-core.negation
open import foundation-core.propositions

open import univalent-combinatorics.2-element-types
```

</details>

## Properties

### The unrestricted law of excluded middle does not hold

```agda
abstract
  no-global-decidability :
    {l : Level} → ¬ ((X : UU l) → is-decidable X)
  no-global-decidability {l} d =
    is-not-decidable-type-2-Element-Type (λ X → d (pr1 X))
```
