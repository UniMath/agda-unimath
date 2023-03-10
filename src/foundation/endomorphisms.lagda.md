# endomorphisms

```agda
module foundation.endomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.endomorphisms public

open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.identity-types
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.monoids
open import group-theory.semigroups

open import structured-types.wild-monoids
```

</details>

## Idea

An endomorphism on a type `A` is a map `A → A`.

## Properties

### Endomorphisms form a monoid

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

endo-Semigroup : {l : Level} → Set l → Semigroup l
pr1 (endo-Semigroup A) = endo-Set A
pr1 (pr2 (endo-Semigroup A)) g f = g ∘ f
pr2 (pr2 (endo-Semigroup A)) h g f = refl

endo-Monoid : {l : Level} → Set l → Monoid l
pr1 (endo-Monoid A) = endo-Semigroup A
pr1 (pr2 (endo-Monoid A)) = id
pr1 (pr2 (pr2 (endo-Monoid A))) f = refl
pr2 (pr2 (pr2 (endo-Monoid A))) f = refl
```

## See also

- For endomorphisms in a category see
  [`category-theory.endomorphisms-of-objects-categories`](category-theory.endomorphisms-of-objects-categories.md).
