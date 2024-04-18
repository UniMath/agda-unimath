# Mere identity endomorphisms

```agda
module foundation.mere-identity-endomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-types
open import foundation.mere-homotopies
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

An [endomorphism](foundation-core.endomorphisms.md) `f : A → A` on a type `A` is said to be a {{#concept "mere identity endomorphism" Agda=mere-identity-endomorphism}} if it is [merely homotopic](foundation.mere-homotopies.md) to the [identity function](foundation-core.function-types.md).

## Definitions

### The predicate of being a mere identity endomorphism

```agda
module _
  {l1 : Level} {A : UU l1} (f : A → A)
  where

  is-mere-identity-endomorphism-Prop : Prop l1
  is-mere-identity-endomorphism-Prop = mere-htpy-Prop id f

  is-mere-identity-endomorphism : UU l1
  is-mere-identity-endomorphism = mere-htpy id f

  is-prop-is-mere-identity-endomorphism :
    is-prop is-mere-identity-endomorphism
  is-prop-is-mere-identity-endomorphism = is-prop-mere-htpy id f
```
