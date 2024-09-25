# Invertible functors between synthetic categories

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.invertible-functors-synthetic-categories where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.globular-types

open import synthetic-category-theory.equivalences-synthetic-categories
open import synthetic-category-theory.retractions-synthetic-categories
open import synthetic-category-theory.sections-synthetic-categories
open import synthetic-category-theory.synthetic-categories
```

</details>

## Idea

A functor f: A → B of [synthetic categories](synthetic-category-theory.synthetic-categories.md) is
{{#concept "invertible" Disambiguation="Synthetic categories"}} if it has an inverse, i.e. if
there exists a functor g: B → A together with natural isomorphisms g∘f ≅ id and g∘f ≅ id.

### The predicate of being an inverse to a functor f: A → B of synthetic categories

```agda
module _
  {l : Level}
  where

  is-inverse-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    (f : functor-Synthetic-Category-Theory κ C D)
    (g : functor-Synthetic-Category-Theory κ D C) → UU l
  is-inverse-Synthetic-Category-Theory κ μ ι f g =
    ( is-section-Synthetic-Category-Theory κ μ ι f g)
      ×
    ( is-retraction-Synthetic-Category-Theory κ μ ι f g)
```

### The predicate of being an invertible functor of synthetic categories

```agda
module _
  {l : Level}
  where

  is-invertible-functor-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    (f : functor-Synthetic-Category-Theory κ C D) → UU l
  is-invertible-functor-Synthetic-Category-Theory κ μ ι f =
    Σ ( functor-Synthetic-Category-Theory κ _ _)
      ( is-inverse-Synthetic-Category-Theory κ μ ι f)
```

### The type of invertible functors between two given synthetic categories

```agda
module _
  {l : Level}
  where

  invertible-functor-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    (C D : category-Synthetic-Category-Theory κ) → UU l
  invertible-functor-Synthetic-Category-Theory κ μ ι C D =
    Σ ( functor-Synthetic-Category-Theory κ C D)
      ( is-invertible-functor-Synthetic-Category-Theory κ μ ι)
```

### The components of an invertible functor of synthetic categories

```agda
module _
  {l : Level}
  where

  functor-invertible-functor-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ} →
    invertible-functor-Synthetic-Category-Theory κ μ ι C D →
    functor-Synthetic-Category-Theory κ C D
  functor-invertible-functor-Synthetic-Category-Theory κ μ ι = pr1
```

### The components of a proof of being an invertible functor of synthetic categories

```agda
  inverse-functor-is-invertible-functor-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D} →
    is-invertible-functor-Synthetic-Category-Theory κ μ ι f →
    functor-Synthetic-Category-Theory κ D C
  inverse-functor-is-invertible-functor-Synthetic-Category-Theory κ μ ι = pr1

  is-inverse-inverse-functor-is-invertible-functor-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D}
    (H : is-invertible-functor-Synthetic-Category-Theory κ μ ι f) →
    is-inverse-Synthetic-Category-Theory κ μ ι f
      ( inverse-functor-is-invertible-functor-Synthetic-Category-Theory κ μ ι H)
  is-inverse-inverse-functor-is-invertible-functor-Synthetic-Category-Theory κ μ ι = pr2

  is-section-inverse-functor-is-invertible-functor-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D}
    (H : is-invertible-functor-Synthetic-Category-Theory κ μ ι f) →
    is-section-Synthetic-Category-Theory κ μ ι f
      ( inverse-functor-is-invertible-functor-Synthetic-Category-Theory κ μ ι H)
  is-section-inverse-functor-is-invertible-functor-Synthetic-Category-Theory κ μ ι H =
    pr1 (is-inverse-inverse-functor-is-invertible-functor-Synthetic-Category-Theory κ μ ι H)

  is-retraction-inverse-functor-is-invertible-functor-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D}
    (H : is-invertible-functor-Synthetic-Category-Theory κ μ ι f) →
    is-retraction-Synthetic-Category-Theory κ μ ι f
      ( inverse-functor-is-invertible-functor-Synthetic-Category-Theory κ μ ι H)
  is-retraction-inverse-functor-is-invertible-functor-Synthetic-Category-Theory κ μ ι H =
    pr2 (is-inverse-inverse-functor-is-invertible-functor-Synthetic-Category-Theory κ μ ι H)

  section-is-invertible-functor-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D} →
    is-invertible-functor-Synthetic-Category-Theory κ μ ι f →
    section-Synthetic-Category-Theory κ μ ι f
  pr1 (section-is-invertible-functor-Synthetic-Category-Theory κ μ ι H) =
    inverse-functor-is-invertible-functor-Synthetic-Category-Theory κ μ ι H
  pr2 (section-is-invertible-functor-Synthetic-Category-Theory κ μ ι H) =
    is-section-inverse-functor-is-invertible-functor-Synthetic-Category-Theory κ μ ι H

  retraction-is-invertible-functor-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D} →
    is-invertible-functor-Synthetic-Category-Theory κ μ ι f →
    retraction-Synthetic-Category-Theory κ μ ι f
  pr1 (retraction-is-invertible-functor-Synthetic-Category-Theory κ μ ι H) =
    inverse-functor-is-invertible-functor-Synthetic-Category-Theory κ μ ι H
  pr2 (retraction-is-invertible-functor-Synthetic-Category-Theory κ μ ι H) =
    is-retraction-inverse-functor-is-invertible-functor-Synthetic-Category-Theory κ μ ι H
```

### A functor f : C → D of synthetic categories is invertible iff it is an equivalence

```agda
module _
  {l : Level}
  where

  is-equiv-is-invertible-functor-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D} →
    is-invertible-functor-Synthetic-Category-Theory κ μ ι f →
    is-equiv-Synthetic-Category-Theory κ μ ι f
  pr1 (is-equiv-is-invertible-functor-Synthetic-Category-Theory κ μ ι H) =
    section-is-invertible-functor-Synthetic-Category-Theory κ μ ι H
  pr2 (is-equiv-is-invertible-functor-Synthetic-Category-Theory κ μ ι H) =
    retraction-is-invertible-functor-Synthetic-Category-Theory κ μ ι H

  is-invertible-functor-is-equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    (ν : inverse-Synthetic-Category-Theory κ μ ι)
    (Λ : left-unit-law-composition-Synthetic-Category-Theory κ ι μ)
    (Ρ : right-unit-law-composition-Synthetic-Category-Theory κ ι μ)
    (X : horizontal-composition-Synthetic-Category-Theory κ μ)
    (Α : associative-composition-Synthetic-Category-Theory κ μ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D} →
    is-equiv-Synthetic-Category-Theory κ μ ι f →
    is-invertible-functor-Synthetic-Category-Theory κ μ ι f
  pr1 (is-invertible-functor-is-equiv-Synthetic-Category-Theory κ μ ι ν Λ Ρ Χ Α B) =
    functor-section-Synthetic-Category-Theory κ μ ι
      ( section-is-equiv-Synthetic-Category-Theory κ μ ι B)
  pr1 (pr2 (is-invertible-functor-is-equiv-Synthetic-Category-Theory κ μ ι ν Λ Ρ Χ Α B)) =
    is-section-functor-section-Synthetic-Category-Theory κ μ ι
      ( section-is-equiv-Synthetic-Category-Theory κ μ ι B)
  pr2 (pr2 (is-invertible-functor-is-equiv-Synthetic-Category-Theory κ μ ι ν Λ Ρ Χ Α B)) =
    comp-iso-Synthetic-Category-Theory μ
      ( is-retraction-functor-retraction-Synthetic-Category-Theory κ μ ι
        ( retraction-is-equiv-Synthetic-Category-Theory κ μ ι B))
      ( horizontal-comp-iso-Synthetic-Category-Theory Χ
        ( comp-iso-Synthetic-Category-Theory μ
          ( comp-iso-Synthetic-Category-Theory μ
            ( comp-iso-Synthetic-Category-Theory μ
              ( comp-iso-Synthetic-Category-Theory μ
                ( right-unit-law-comp-functor-Synthetic-Category-Theory Ρ
                  ( functor-retraction-Synthetic-Category-Theory κ μ ι
                    ( retraction-is-equiv-Synthetic-Category-Theory κ μ ι B)))
                ( horizontal-comp-iso-Synthetic-Category-Theory Χ
                  ( id-iso-Synthetic-Category-Theory ι
                    ( functor-retraction-Synthetic-Category-Theory κ μ ι
                      ( retraction-is-equiv-Synthetic-Category-Theory κ μ ι B)))
                  ( is-section-functor-section-Synthetic-Category-Theory κ μ ι
                    ( section-is-equiv-Synthetic-Category-Theory κ μ ι B))))
              ( associative-comp-functor-Synthetic-Category-Theory Α
                ( functor-retraction-Synthetic-Category-Theory κ μ ι
                  ( retraction-is-equiv-Synthetic-Category-Theory κ μ ι B))
                ( _)
                ( functor-section-Synthetic-Category-Theory κ μ ι
                  ( section-is-equiv-Synthetic-Category-Theory κ μ ι B))))
            ( horizontal-comp-iso-Synthetic-Category-Theory Χ
              ( inv-iso-Synthetic-Category-Theory ν
                ( is-retraction-functor-retraction-Synthetic-Category-Theory κ μ ι
                  ( retraction-is-equiv-Synthetic-Category-Theory κ μ ι B)))
              ( id-iso-Synthetic-Category-Theory ι
                ( functor-section-Synthetic-Category-Theory κ μ ι
                  ( section-is-equiv-Synthetic-Category-Theory κ μ ι B)))))
          ( inv-iso-Synthetic-Category-Theory ν
            ( left-unit-law-comp-functor-Synthetic-Category-Theory Λ
              ( functor-section-Synthetic-Category-Theory κ μ ι
                ( section-is-equiv-Synthetic-Category-Theory κ μ ι B)))))
        ( id-iso-Synthetic-Category-Theory ι _))
```

### Invertible functors of synthetic categories are closed under composition.

```agda
module _
  {l : Level}
  where

  is-invertible-functor-comp-is-invertible-functor-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    (ν : inverse-Synthetic-Category-Theory κ μ ι)
    (Λ : left-unit-law-composition-Synthetic-Category-Theory κ ι μ)
    (Ρ : right-unit-law-composition-Synthetic-Category-Theory κ ι μ)
    (Χ : horizontal-composition-Synthetic-Category-Theory κ μ)
    (Α : associative-composition-Synthetic-Category-Theory κ μ)
    {C D E : category-Synthetic-Category-Theory κ}
    {f' : functor-Synthetic-Category-Theory κ D E}
    {f : functor-Synthetic-Category-Theory κ C D} →
    is-invertible-functor-Synthetic-Category-Theory κ μ ι f' →
    is-invertible-functor-Synthetic-Category-Theory κ μ ι f →
    is-invertible-functor-Synthetic-Category-Theory κ μ ι
      ( comp-functor-Synthetic-Category-Theory μ f' f)
  pr1 (is-invertible-functor-comp-is-invertible-functor-Synthetic-Category-Theory κ μ ι ν Λ Ρ Χ Α K H) =
    comp-functor-Synthetic-Category-Theory μ _ _
  pr1 (pr2 (is-invertible-functor-comp-is-invertible-functor-Synthetic-Category-Theory κ μ ι ν Λ Ρ Χ Α K H)) =
    comp-iso-Synthetic-Category-Theory μ
      ( is-section-functor-section-Synthetic-Category-Theory κ μ ι
        ( section-is-invertible-functor-Synthetic-Category-Theory κ μ ι K))
      ( comp-iso-Synthetic-Category-Theory μ
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( right-unit-law-comp-functor-Synthetic-Category-Theory Ρ _)
          ( id-iso-Synthetic-Category-Theory ι
            ( _)))
        ( comp-iso-Synthetic-Category-Theory μ
          ( horizontal-comp-iso-Synthetic-Category-Theory Χ
            ( horizontal-comp-iso-Synthetic-Category-Theory Χ
              ( id-iso-Synthetic-Category-Theory ι _)
              ( is-section-functor-section-Synthetic-Category-Theory κ μ ι
                ( section-is-invertible-functor-Synthetic-Category-Theory κ μ ι H)))
            ( id-iso-Synthetic-Category-Theory ι _))
          ( comp-iso-Synthetic-Category-Theory μ
            ( horizontal-comp-iso-Synthetic-Category-Theory Χ
              ( associative-comp-functor-Synthetic-Category-Theory Α _ _ _)
              ( id-iso-Synthetic-Category-Theory ι _))
            ( inv-iso-Synthetic-Category-Theory ν
              ( associative-comp-functor-Synthetic-Category-Theory Α
                ( comp-functor-Synthetic-Category-Theory μ _ _)
                ( _)
                ( _))))))
  pr2 (pr2 (is-invertible-functor-comp-is-invertible-functor-Synthetic-Category-Theory κ μ ι ν Λ Ρ Χ Α K H)) =
    comp-iso-Synthetic-Category-Theory μ
      ( is-retraction-functor-retraction-Synthetic-Category-Theory κ μ ι
        ( retraction-is-invertible-functor-Synthetic-Category-Theory κ μ ι H))
      ( comp-iso-Synthetic-Category-Theory μ
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( right-unit-law-comp-functor-Synthetic-Category-Theory Ρ _)
          ( id-iso-Synthetic-Category-Theory ι _))
        ( comp-iso-Synthetic-Category-Theory μ
          ( horizontal-comp-iso-Synthetic-Category-Theory Χ
            ( horizontal-comp-iso-Synthetic-Category-Theory Χ
              ( id-iso-Synthetic-Category-Theory ι _)
              ( is-retraction-functor-retraction-Synthetic-Category-Theory κ μ ι
                ( retraction-is-invertible-functor-Synthetic-Category-Theory κ μ ι K)))
            ( id-iso-Synthetic-Category-Theory ι _))
          ( comp-iso-Synthetic-Category-Theory μ
            ( horizontal-comp-iso-Synthetic-Category-Theory Χ
              ( associative-comp-functor-Synthetic-Category-Theory Α _ _ _)
              ( id-iso-Synthetic-Category-Theory ι _))
            ( inv-iso-Synthetic-Category-Theory ν
              ( associative-comp-functor-Synthetic-Category-Theory Α
                ( comp-functor-Synthetic-Category-Theory μ _ _)
                ( _)
                ( _))))))
```
