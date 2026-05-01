# The subuniverse of contractible types

```agda
module foundation.subuniverse-of-contractible-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.identity-types
```

</details>

## Idea

We show that being [contractible](foundation-core.contractible-types.md) is a
[property](foundation-core.propositions.md), and thus we obtain a
[subuniverse](foundation.subuniverses.md) of contractible types.

## Definition

### The subuniverse of contractible types

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-contr-is-contr : is-contr A → is-contr (is-contr A)
    is-contr-is-contr (pair a α) =
      is-contr-Σ
        ( pair a α)
        ( a)
        ( is-contr-Π (is-prop-is-contr (pair a α) a))

  abstract
    is-property-is-contr : (H K : is-contr A) → is-contr (H ＝ K)
    is-property-is-contr H = is-prop-is-contr (is-contr-is-contr H) H
```
