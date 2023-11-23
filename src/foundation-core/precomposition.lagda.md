# Precomposition

```agda
module foundation-core.precomposition where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.dependent-homotopies
open import foundation.universe-levels

open import foundation-core.homotopies
```

</details>

## Idea

Given a function `f : A → B` and a type family `X` over `B`, the
**precomposition function**

```text
  - ∘ f : ((y : B) → X b) → ((x : A) → X (f x))
```

is defined by `λ h x → h (f x)`. The precomposition function takes a simpler
form without dependent types: Given a type `X` the precomposition function by
`f`

```text
  - ∘ f : (B → X) → (A → X)
```

is given by `λ h x → h (f x)`.

## Definitions

### The dependent precomposition function

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3)
  where

  precomp-Π : ((b : B) → C b) → ((a : A) → C (f a))
  precomp-Π h a = h (f a)
```

### The (nondependent) precomposition function

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : UU l3)
  where

  precomp : (B → C) → (A → C)
  precomp = precomp-Π f (λ b → C)
```

## Properties

### The action of dependent precomposition on homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {f g : A → B} (H : f ~ g) (C : B → UU l3) (h : (y : B) → C y)
  where

  htpy-precomp-Π :
    dependent-homotopy (λ _ → C) H (precomp-Π f C h) (precomp-Π g C h)
  htpy-precomp-Π x = apd h (H x)
```
