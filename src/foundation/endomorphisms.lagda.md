# Endomorphisms

```agda
module foundation.endomorphisms where

open import foundation-core.endomorphisms public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.sets

open import group-theory.monoids
open import group-theory.semigroups

open import structured-types.h-spaces
open import structured-types.wild-monoids
```

</details>

## Idea

An {{#concept "endomorphism"}} on a type `A` is a function `A → A`. The type of
endomorphisms on `A` is an [H-space](structured-types.h-spaces.md). Note that the
unit laws for function composition hold judgmentally, so
[function extensionality](foundation.function-extensionality.md) is not required
to establish the H-space structure on the type of endomorphisms `A → A`.
Furthermore, since function composition is strictly associative, the type of
endomorphisms `A → A` is also a [wild monoid](structured-types.wild-monoids.md).

## Properties

### The type of endomorphisms on any type is an H-space

```agda
module _
  {l : Level} (A : UU l)
  where

  endo-H-Space : H-Space l
  pr1 endo-H-Space = endo-Pointed-Type A
  pr1 (pr2 endo-H-Space) g f = g ∘ f
  pr1 (pr2 (pr2 endo-H-Space)) f = refl
  pr1 (pr2 (pr2 (pr2 endo-H-Space))) f = refl
  pr2 (pr2 (pr2 (pr2 endo-H-Space))) = refl
```

### The type of endomorphisms form a wild monoid

```agda
endo-Wild-Monoid : {l : Level} → UU l → Wild-Monoid l
pr1 (pr1 (endo-Wild-Monoid A)) = endo-Pointed-Type A
pr1 (pr2 (pr1 (endo-Wild-Monoid A))) g f = g ∘ f
pr1 (pr2 (pr2 (pr1 (endo-Wild-Monoid A)))) f = refl
pr1 (pr2 (pr2 (pr2 (pr1 (endo-Wild-Monoid A))))) f = refl
pr2 (pr2 (pr2 (pr2 (pr1 (endo-Wild-Monoid A))))) = refl
pr1 (pr2 (endo-Wild-Monoid A)) h g f = refl
pr1 (pr2 (pr2 (endo-Wild-Monoid A))) g f = refl
pr1 (pr2 (pr2 (pr2 (endo-Wild-Monoid A)))) g f = refl
pr1 (pr2 (pr2 (pr2 (pr2 (endo-Wild-Monoid A))))) g f = refl
pr2 (pr2 (pr2 (pr2 (pr2 (endo-Wild-Monoid A))))) = star
```

### The type of endomorphisms on a set form a semigroup

```agda
endo-Semigroup : {l : Level} → Set l → Semigroup l
pr1 (endo-Semigroup A) = endo-Set A
pr1 (pr2 (endo-Semigroup A)) g f = g ∘ f
pr2 (pr2 (endo-Semigroup A)) h g f = refl
```

### The type of endomorphisms on a set form a monoid

```agda
endo-Monoid : {l : Level} → Set l → Monoid l
pr1 (endo-Monoid A) = endo-Semigroup A
pr1 (pr2 (endo-Monoid A)) = id
pr1 (pr2 (pr2 (endo-Monoid A))) f = refl
pr2 (pr2 (pr2 (endo-Monoid A))) f = refl
```

## See also

- For endomorphisms in a category see
  [`category-theory.endomorphisms-in-categories`](category-theory.endomorphisms-in-categories.md).
- [Mere identity endomorphisms](foundation.mere-identity-endomorphisms.md)
