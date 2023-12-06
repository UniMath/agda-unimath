# Precomposition of type families

```agda
module foundation.precomposition-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

Any map `f : A → B` induces a
{{#concept "precomposition operation" Disambiguation="of type families"}}

```text
  (B → 𝒰) → (A → 𝒰)
```

given by [precomposing](foundation-core.precomposition-functions.md) any
`Q : B → 𝒰` to `Q ∘ f : A → 𝒰`.

## Definitions

### The precomposition operation on type familes

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  precomp-family : (l : Level) → (B → UU l) → (A → UU l)
  precomp-family l Q = Q ∘ f
```
