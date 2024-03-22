# Postcomposition of functions

```agda
module foundation-core.postcomposition-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.postcomposition-dependent-functions
```

</details>

## Idea

Given a map `f : X → Y` and a type `A`, the
{{#concept "postcomposition function" Agda=postcomp}}

```text
  f ∘ - : (A → X) → (A → Y)
```

is defined by `λ h x → f (h x)`.

## Definitions

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) {X : UU l2} {Y : UU l3}
  where

  postcomp : (X → Y) → (A → X) → (A → Y)
  postcomp f = postcomp-Π A f
```
