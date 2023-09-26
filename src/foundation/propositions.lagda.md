# Propositions

<details><summary>Imports</summary>
```agda
module foundation.propositions where
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-extensionality
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.propositions public
open import foundation-core.retractions
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
open import foundation-core.universe-levels
open import foundation.contractible-types
```
</details>

### Propositions are (k+1)-truncated for any k

```agda
abstract
  is-trunc-is-prop :
    {l : Level} (k : 𝕋) {A : UU l} → is-prop A → is-trunc (succ-𝕋 k) A
  is-trunc-is-prop k is-prop-A x y = is-trunc-is-contr k (is-prop-A x y)
```

### Propositions are closed under retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : UU l2)
  where

  is-prop-retract-of : A retract-of B → is-prop B → is-prop A
  is-prop-retract-of = is-trunc-retract-of
```

### Two equivalent types are equivalently propositions

```agda
equiv-is-prop-equiv : {l1 l2 : Level} {A : UU l1} {B : UU l2}
  → A ≃ B → is-prop A ≃ is-prop B
equiv-is-prop-equiv {A = A} {B = B} e =
  equiv-prop
    (is-prop-is-prop A)
    (is-prop-is-prop B)
    (is-prop-equiv' e)
    (is-prop-equiv e)
```
