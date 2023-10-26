# Functors between set-magmoids

```agda
module category-theory.functors-set-magmoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.set-magmoids

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A **functor between [set-magmoids](category-theory.set-magmoids.md)** is a
family of maps on the hom-[sets](foundation-core.sets.md) that preserve the
[composition operation](category-theory.composition-operations-on-binary-families-of-sets.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Set-Magmoid l1 l2) (B : Set-Magmoid l3 l4)
  (F₀ : obj-Set-Magmoid A → obj-Set-Magmoid B)
  (F₁ :
    {x y : obj-Set-Magmoid A} →
    hom-Set-Magmoid A x y → hom-Set-Magmoid B (F₀ x) (F₀ y))
  where

  preserves-comp-functor-Set-Magmoid : UU (l1 ⊔ l2 ⊔ l4)
  preserves-comp-functor-Set-Magmoid =
    {x y z : obj-Set-Magmoid A}
    (g : hom-Set-Magmoid A y z) (f : hom-Set-Magmoid A x y) →
    F₁ (comp-hom-Set-Magmoid A g f) ＝ comp-hom-Set-Magmoid B (F₁ g) (F₁ f)

  is-prop-preserves-comp-functor-Set-Magmoid :
    is-prop preserves-comp-functor-Set-Magmoid
  is-prop-preserves-comp-functor-Set-Magmoid =
    is-prop-iterated-implicit-Π 3
      ( λ x y z →
        is-prop-iterated-Π 2
          ( λ g f →
            is-set-hom-Set-Magmoid B (F₀ x) (F₀ z)
              ( F₁ (comp-hom-Set-Magmoid A g f))
              ( comp-hom-Set-Magmoid B (F₁ g) (F₁ f))))

  preserves-comp-prop-functor-Set-Magmoid :
    Prop (l1 ⊔ l2 ⊔ l4)
  pr1 preserves-comp-prop-functor-Set-Magmoid =
    preserves-comp-functor-Set-Magmoid
  pr2 preserves-comp-prop-functor-Set-Magmoid =
    is-prop-preserves-comp-functor-Set-Magmoid

module _
  {l1 l2 l3 l4 : Level}
  (A : Set-Magmoid l1 l2) (B : Set-Magmoid l3 l4)
  where

  functor-Set-Magmoid : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  functor-Set-Magmoid =
    Σ ( obj-Set-Magmoid A → obj-Set-Magmoid B)
      ( λ F₀ →
        Σ ( {x y : obj-Set-Magmoid A} →
            hom-Set-Magmoid A x y → hom-Set-Magmoid B (F₀ x) (F₀ y))
          ( preserves-comp-functor-Set-Magmoid A B F₀))
```

### The identity morphism of composition operations on binary families of sets

```agda
module _
  {l1 l2 : Level} (A : Set-Magmoid l1 l2)
  where

  id-functor-Set-Magmoid :
    functor-Set-Magmoid A A
  pr1 id-functor-Set-Magmoid = id
  pr1 (pr2 id-functor-Set-Magmoid) = id
  pr2 (pr2 id-functor-Set-Magmoid) g f = refl
```
