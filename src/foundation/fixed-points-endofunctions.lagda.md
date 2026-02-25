# Fixed points of endofunctions

```agda
module foundation.fixed-points-endofunctions where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

Given an [endofunction](foundation-core.endomorphisms.md) `f : A → A`, the type
of
{{#concept "fixed points" Disambiguation="of an endofunction" Agda=fixed-point}}
is the type of elements `x : A` such that `f x ＝ x`

```text
  fixed-point f := Σ (x : A), (f x ＝ x).
```

## Definitions

```agda
module _
  {l : Level} {A : UU l} (f : A → A)
  where

  fixed-point : UU l
  fixed-point = Σ A (λ x → f x ＝ x)

  fixed-point' : UU l
  fixed-point' = Σ A (λ x → x ＝ f x)
```
