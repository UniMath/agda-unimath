# Mere identity endomorphisms

```agda
module foundation.mere-identity-endomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.mere-homotopies
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.equivalences
```

</details>

## Idea

An [endomorphism](foundation-core.endomorphisms.md) `f : A → A` on a type `A` is
said to be a
{{#concept "mere identity endomorphism" Agda=mere-identity-endomorphism}} if it
is [merely homotopic](foundation.mere-homotopies.md) to the
[identity function](foundation-core.function-types.md).

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

### Mere identity endomorphisms

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  mere-identity-endomorphism : UU l1
  mere-identity-endomorphism = Σ (A → A) is-mere-identity-endomorphism

  module _
    {e : mere-identity-endomorphism}
    where

    endomorphism-mere-identity-endomorphism : A → A
    endomorphism-mere-identity-endomorphism = pr1 e

    is-mere-identity-mere-identity-endomorphism :
      is-mere-identity-endomorphism endomorphism-mere-identity-endomorphism
    is-mere-identity-mere-identity-endomorphism = pr2 e
```

### The predicate of being a mere identity automorphism

```agda
module _
  {l1 : Level} {A : UU l1} (e : A ≃ A)
  where

  is-mere-identity-automorphism-Prop : Prop l1
  is-mere-identity-automorphism-Prop = mere-htpy-Prop id (map-equiv e)

  is-mere-identity-automorphism : UU l1
  is-mere-identity-automorphism = mere-htpy id (map-equiv e)

  is-prop-is-mere-identity-automorphism :
    is-prop is-mere-identity-automorphism
  is-prop-is-mere-identity-automorphism = is-prop-mere-htpy id (map-equiv e)
```

### Mere identity automorphisms

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  mere-identity-automorphism : UU l1
  mere-identity-automorphism = Σ (A ≃ A) is-mere-identity-automorphism

  module _
    {e : mere-identity-automorphism}
    where

    automorphism-mere-identity-automorphism : A ≃ A
    automorphism-mere-identity-automorphism = pr1 e

    is-mere-identity-mere-identity-automorphism :
      is-mere-identity-automorphism automorphism-mere-identity-automorphism
    is-mere-identity-mere-identity-automorphism = pr2 e
```

## Properties

### The type of mere identity endomorphisms is connected

