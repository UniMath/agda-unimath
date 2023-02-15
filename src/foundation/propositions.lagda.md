#  Propositions

```agda
module foundation.propositions where

open import foundation-core.propositions public

open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-extensionality
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
open import foundation-core.universe-levels

open import foundation.contractible-types
```

### Propositions are (k+1)-truncated for any k.

```agda
abstract
  is-trunc-is-prop :
    { l : Level} (k : 𝕋) {A : UU l} → is-prop A → is-trunc (succ-𝕋 k) A
  is-trunc-is-prop k is-prop-A x y = is-trunc-is-contr k (is-prop-A x y)
```
