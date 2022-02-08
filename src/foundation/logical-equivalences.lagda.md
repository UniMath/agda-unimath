# Logical equivalences

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.logical-equivalences where

open import foundation-core.logical-equivalences public

open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.equivalences using (is-equiv; _≃_)
open import foundation-core.universe-levels using (Level; UU)

open import foundation.propositions using
  ( UU-Prop; is-prop; is-prop-prod; is-prop-function-type; is-prop-type-Prop;
    is-equiv-is-prop; is-prop-type-equiv-Prop; type-Prop)
```

## Properties

### The type of logical equivalences between propositions is a proposition

```agda
abstract
  is-prop-iff :
    {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) → is-prop (P ⇔ Q)
  is-prop-iff P Q =
    is-prop-prod
      ( is-prop-function-type (is-prop-type-Prop Q))
      ( is-prop-function-type (is-prop-type-Prop P))
```

### Logical equivalence of propositions is equivalent to equivalence of propositions

```agda
abstract
  is-equiv-equiv-iff :
    {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
    is-equiv (equiv-iff' P Q)
  is-equiv-equiv-iff P Q =
    is-equiv-is-prop
      ( is-prop-iff P Q)
      ( is-prop-type-equiv-Prop P Q)
      ( iff-equiv P Q)

equiv-equiv-iff :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  (P ⇔ Q) ≃ (type-Prop P ≃ type-Prop Q)
pr1 (equiv-equiv-iff P Q) = equiv-iff' P Q
pr2 (equiv-equiv-iff P Q) = is-equiv-equiv-iff P Q
```
