# Identity types of truncated types

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.identity-truncated-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-truncated-types funext
open import foundation.univalence funext univalence
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

### The type of identity of truncated types is truncated

```agda
module _
  {l : Level} {A B : UU l}
  where

  is-trunc-id-is-trunc :
    (k : 𝕋) → is-trunc k A → is-trunc k B → is-trunc k (A ＝ B)
  is-trunc-id-is-trunc k is-trunc-A is-trunc-B =
    is-trunc-equiv k
      ( A ≃ B)
      ( equiv-univalence)
      ( is-trunc-equiv-is-trunc k is-trunc-A is-trunc-B)
```
