# Postcomposition of dependent functions

```agda
module foundation-core.postcomposition-dependent-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

Given a type `A` and a family of maps `f : {a : A} → X a → Y a`, the
{{#concept "postcomposition function" Disambiguation="of dependent functions by a family of maps" Agda=postcomp-Π}}
of dependent functions `(a : A) → X a` by the family of maps `f`

```text
  postcomp-Π A f : ((a : A) → X a) → ((a : A) → Y a)
```

is defined by `λ h x → f (h x)`.

Note that, since the definition of the family of maps `f` depends on the base
`A`, postcomposition of dependent functions does not generalize
[postcomposition of functions](foundation-core.postcomposition-functions.md) in
the same way that
[precomposition of dependent functions](foundation-core.precomposition-dependent-functions.md)
generalizes
[precomposition of functions](foundation-core.precomposition-functions.md). If
`A` can vary while keeping `f` fixed, we have necessarily reduced to the case of
[postcomposition of functions](foundation-core.postcomposition-functions.md).

## Definitions

### Postcomposition of dependent functions

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) {X : A → UU l2} {Y : A → UU l3}
  where

  postcomp-Π : ({a : A} → X a → Y a) → ((a : A) → X a) → ((a : A) → Y a)
  postcomp-Π f = f ∘_
```
