# Anafunctors

```agda
{-# OPTIONS --without-K --exact-split #-}

module category-theory.anafunctors where

open import category-theory.categories using (Cat; precat-Cat)
open import category-theory.precategories using
  ( Precat; obj-Precat; type-hom-Precat; id-Precat; comp-Precat)

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id)
open import foundation.propositional-truncations using (type-trunc-Prop)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)
```

## Idea

An anafunctor is a functor that is only defined up to isomorphism.

## Definition

### Anafunctors between precategories

```agda
anafunctor-Precat :
  {l1 l2 l3 l4 : Level} (l : Level) →
  Precat l1 l2 → Precat l3 l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
anafunctor-Precat l C D =
  Σ ( obj-Precat C → obj-Precat D → UU l)
    ( λ F₀ →
      Σ ( (X Y : obj-Precat C) (U : obj-Precat D) (u : F₀ X U) →
          (V : obj-Precat D) (v : F₀ Y V) →
          (f : type-hom-Precat C X Y) → type-hom-Precat D U V)
        ( λ  F₁ →
          ( ( X : obj-Precat C) → type-trunc-Prop (Σ (obj-Precat D) (F₀ X))) ×
          ( ( ( X : obj-Precat C) (U : obj-Precat D) (u : F₀ X U) →
              Id (F₁ X X U u U u (id-Precat C)) (id-Precat D)) ×
            ( ( X Y Z : obj-Precat C)
              ( U : obj-Precat D) (u : F₀ X U) (V : obj-Precat D) (v : F₀ Y V)
              ( W : obj-Precat D) (w : F₀ Z W) →
              ( g : type-hom-Precat C Y Z) (f : type-hom-Precat C X Y) →
              Id ( F₁ X Z U u W w (comp-Precat C g f))
                 ( comp-Precat D
                   ( F₁ Y Z V v W w g)
                   ( F₁ X Y U u V v f))))))
```

### Anafunctors between categories

```agda
anafunctor-Cat :
  {l1 l2 l3 l4 : Level} (l : Level) →
  Cat l1 l2 → Cat l3 l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
anafunctor-Cat l C D = anafunctor-Precat l (precat-Cat C) (precat-Cat D)
```
