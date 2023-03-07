# Constant maps

```agda
{-# OPTIONS --safe #-}
```

```agda
module foundation-core.constant-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.universe-levels
```

</details>

## Definition

```agda
const : {i j : Level} (A : UU i) (B : UU j) (b : B) → A → B
const A B b x = b
```
