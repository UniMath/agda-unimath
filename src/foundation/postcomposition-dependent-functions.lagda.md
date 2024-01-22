# Postcomposition of dependent functions

```agda
module foundation.postcomposition-dependent-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

Given a type `A` and a dependent map `f : {a : A} → X a → Y a`, the
{{#concept "dependent postcomposition function" Agda=postcomp-Π}}

```text
  f ∘ - : ((a : A) → X a) → ((a : A) → Y a)
```

is defined by `λ h x → f (h x)`.

Note that, as opposed to
[precomposition of dependent functions](foundation-core.precomposition-dependent-functions.md),
the use-case for postcomposition of dependent functions is very limited, since
the definition of `f` depends on the particular choice of `A`. Once we allow `A`
to vary while keeping `f` fixed, we reduce to the case of
[postcomposition of (nondependent) functions](foundation-core.postcomposition-functions.md).

## Definitions

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) {X : A → UU l2} {Y : A → UU l3}
  where

  postcomp-Π : ({a : A} → X a → Y a) → ((a : A) → X a) → ((a : A) → Y a)
  postcomp-Π f = f ∘_
```
