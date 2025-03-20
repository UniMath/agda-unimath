# Truncated equality

```agda
open import foundation.function-extensionality-axiom

module
  foundation.truncated-equality
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.truncations funext
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Definition

```agda
trunc-eq : {l : Level} (k : 𝕋) {A : UU l} → A → A → Truncated-Type l k
trunc-eq k x y = trunc k (x ＝ y)
```
