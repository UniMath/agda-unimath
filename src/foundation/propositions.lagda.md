# Propositions

```agda
module foundation.propositions where

open import foundation-core.propositions public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.iterated-dependent-product-types
open import foundation.telescopes
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
```

### Propositions are closed under retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : UU l2)
  where

  is-prop-retract-of : A retract-of B → is-prop B → is-prop A
  is-prop-retract-of = is-trunc-retract-of
```

### Iterated products of propositions are propositions

```agda
is-prop-iterated-Π :
  {l : Level} (n : ℕ) {{A : telescope l n}} →
  transform-iterated-Π is-prop A → is-prop (iterated-Π A)
is-prop-iterated-Π ._ {{base-telescope A}} H = H
is-prop-iterated-Π ._ {{cons-telescope A}} H =
  is-prop-Π (λ x → is-prop-iterated-Π _ {{A x}} (H x))
```
