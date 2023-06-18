# Large identity types

```agda
module foundation.large-identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Definition

```agda
module _
  {A : UUω}
  where

  data Idω (x : A) : A → UUω where
    reflω : Idω x x

  _＝ω_ : A → A → UUω
  (a ＝ω b) = Idω a b
```
