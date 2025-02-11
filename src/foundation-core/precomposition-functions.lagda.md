# Precomposition of functions

```agda
module foundation-core.precomposition-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

Given a function `f : A → B` and a type `X`, the **precomposition function** by
`f`

```text
  - ∘ f : (B → X) → (A → X)
```

is defined by `λ h x → h (f x)`.

## Definitions

### The precomposition operation on ordinary functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : UU l3)
  where

  precomp : (B → C) → (A → C)
  precomp = _∘ f
```
