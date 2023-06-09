# Constant maps

```agda
module foundation-core.constant-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Definition

```agda
const : {l1 l2 : Level} (A : UU l1) (B : UU l2) → B → A → B
const A B b x = b
```
