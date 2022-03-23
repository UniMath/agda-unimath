# Anafunctors

```agda
{-# OPTIONS --without-K --exact-split #-}

module category-theory.anafunctors where

open import category-theory.categories using
  ( Cat; precat-Cat; obj-Cat; type-hom-Cat)
open import category-theory.functors-precategories using
  ( functor-Precat; obj-functor-Precat; hom-functor-Precat;
    respects-id-functor-Precat; respects-comp-functor-Precat)
open import category-theory.isomorphisms-precategories using
  ( iso-Precat; hom-iso-Precat; hom-inv-iso-Precat; id-iso-Precat;
    issec-hom-inv-iso-Precat; isretr-hom-inv-iso-Precat)
open import category-theory.precategories using
  ( Precat; obj-Precat; type-hom-Precat; id-hom-Precat; comp-hom-Precat;
    comp-hom-Precat'; right-unit-law-comp-hom-Precat; assoc-comp-hom-Precat)

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.existential-quantification using (∃)
open import foundation.identity-types using (Id; ap; _∙_; inv)
open import foundation.propositional-truncations using
  ( type-trunc-Prop; unit-trunc-Prop)
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
              Id (F₁ X X U u U u (id-hom-Precat C)) (id-hom-Precat D)) ×
            ( ( X Y Z : obj-Precat C)
              ( U : obj-Precat D) (u : F₀ X U) (V : obj-Precat D) (v : F₀ Y V)
              ( W : obj-Precat D) (w : F₀ Z W) →
              ( g : type-hom-Precat C Y Z) (f : type-hom-Precat C X Y) →
              Id ( F₁ X Z U u W w (comp-hom-Precat C g f))
                 ( comp-hom-Precat D
                   ( F₁ Y Z V v W w g)
                   ( F₁ X Y U u V v f))))))

module _
  {l1 l2 l3 l4 l5 : Level} (C : Precat l1 l2) (D : Precat l3 l4)
  (F : anafunctor-Precat l5 C D)
  where
  
  object-anafunctor-Precat : obj-Precat C → obj-Precat D → UU l5
  object-anafunctor-Precat = pr1 F

  hom-anafunctor-Precat :
    (X Y : obj-Precat C) (U : obj-Precat D) (u : object-anafunctor-Precat X U)
    (V : obj-Precat D) (v : object-anafunctor-Precat Y V) →
    type-hom-Precat C X Y → type-hom-Precat D U V
  hom-anafunctor-Precat = pr1 (pr2 F)
```

### Anafunctors between categories

```agda
anafunctor-Cat :
  {l1 l2 l3 l4 : Level} (l : Level) →
  Cat l1 l2 → Cat l3 l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
anafunctor-Cat l C D = anafunctor-Precat l (precat-Cat C) (precat-Cat D)

module _
  {l1 l2 l3 l4 l5 : Level} (C : Cat l1 l2) (D : Cat l3 l4)
  (F : anafunctor-Cat l5 C D)
  where
  
  object-anafunctor-Cat : obj-Cat C → obj-Cat D → UU l5
  object-anafunctor-Cat =
    object-anafunctor-Precat (precat-Cat C) (precat-Cat D) F

  hom-anafunctor-Cat :
    (X Y : obj-Cat C) (U : obj-Cat D) (u : object-anafunctor-Cat X U)
    (V : obj-Cat D) (v : object-anafunctor-Cat Y V) →
    type-hom-Cat C X Y → type-hom-Cat D U V
  hom-anafunctor-Cat =
    hom-anafunctor-Precat (precat-Cat C) (precat-Cat D) F
```

## Properties

### Any functor between precategories induces an anafunctor

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precat l1 l2) (D : Precat l3 l4)
  where
  
  anafunctor-functor-Precat : functor-Precat C D → anafunctor-Precat l4 C D
  pr1 (anafunctor-functor-Precat F) X Y =
    iso-Precat D (obj-functor-Precat C D F X) Y
  pr1 (pr2 (anafunctor-functor-Precat F)) X Y U u V v f =
    comp-hom-Precat D
      ( comp-hom-Precat D
        ( hom-iso-Precat D v)
        ( hom-functor-Precat C D F f))
      ( hom-inv-iso-Precat D u)
  pr1 (pr2 (pr2 (anafunctor-functor-Precat F))) X =
    unit-trunc-Prop (pair (obj-functor-Precat C D F X) (id-iso-Precat D))
  pr1 (pr2 (pr2 (pr2 (anafunctor-functor-Precat F)))) X U u =
    ( ap
      ( comp-hom-Precat' D (hom-inv-iso-Precat D u))
      ( ( ap
          ( comp-hom-Precat D (hom-iso-Precat D u))
          ( respects-id-functor-Precat C D F X)) ∙
        ( right-unit-law-comp-hom-Precat D (hom-iso-Precat D u)))) ∙
    ( issec-hom-inv-iso-Precat D u)
  pr2 (pr2 (pr2 (pr2 (anafunctor-functor-Precat F)))) X Y Z U u V v W w g f =
    ( ap
      ( comp-hom-Precat' D (hom-inv-iso-Precat D u))
      ( ( ( ap
            ( comp-hom-Precat D (hom-iso-Precat D w))
            ( respects-comp-functor-Precat C D F g f)) ∙
          ( ( inv
              ( assoc-comp-hom-Precat D
                ( hom-iso-Precat D w)
                ( hom-functor-Precat C D F g)
                ( hom-functor-Precat C D F f))) ∙
            ( ap
              ( comp-hom-Precat' D (hom-functor-Precat C D F f))
              ( ( inv
                  ( right-unit-law-comp-hom-Precat D
                    ( comp-hom-Precat D
                      ( hom-iso-Precat D w)
                      ( hom-functor-Precat C D F g)))) ∙
                ( ( ap
                    ( comp-hom-Precat D
                      ( comp-hom-Precat D
                        ( hom-iso-Precat D w)
                        ( hom-functor-Precat C D F g)))
                      ( inv (isretr-hom-inv-iso-Precat D v))) ∙
                  ( inv
                    ( assoc-comp-hom-Precat D
                      ( comp-hom-Precat D
                        ( hom-iso-Precat D w)
                        ( hom-functor-Precat C D F g))
                      ( hom-inv-iso-Precat D v)
                      ( hom-iso-Precat D v)))))))) ∙
        ( assoc-comp-hom-Precat D
          ( comp-hom-Precat D
            ( comp-hom-Precat D (hom-iso-Precat D w) (hom-functor-Precat C D F g))
            ( hom-inv-iso-Precat D v))
          ( hom-iso-Precat D v)
          ( hom-functor-Precat C D F f)))) ∙
    ( assoc-comp-hom-Precat D
      ( comp-hom-Precat D
        ( comp-hom-Precat D (hom-iso-Precat D w) (hom-functor-Precat C D F g))
        ( hom-inv-iso-Precat D v))
      ( comp-hom-Precat D (hom-iso-Precat D v) (hom-functor-Precat C D F f))
      ( hom-inv-iso-Precat D u))
```

### The action on objects

```agda
image-object-anafunctor-Cat :
  {l1 l2 l3 l4 l5 : Level} (C : Cat l1 l2) (D : Cat l3 l4) →
  anafunctor-Cat l5 C D → obj-Cat C → UU (l3 ⊔ l5)
image-object-anafunctor-Cat C D F X =
  Σ (obj-Cat D) (λ U → type-trunc-Prop (object-anafunctor-Cat C D F X U))
```
