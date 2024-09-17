# Equivalences of synthetic categories

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.equivalences-synthetic-categories where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.globular-types

open import synthetic-category-theory.synthetic-categories
open import synthetic-category-theory.sections-synthetic-categories
open import synthetic-category-theory.retractions-synthetic-categories
open import synthetic-category-theory.biinvertible-maps-synthetic-categories
```

</details>

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

```agda
module _
  {l : Level}
  where

  is-equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    (f : functor-Synthetic-Category-Theory κ C D) → UU l
  is-equiv-Synthetic-Category-Theory κ μ ι f =
    Σ ( functor-Synthetic-Category-Theory κ _ _)
      λ g →
        ( is-inverse-Synthetic-Category-Theory κ μ ι f g)

  inverse-is-equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D} →
    is-equiv-Synthetic-Category-Theory κ μ ι f →
      functor-Synthetic-Category-Theory κ D C
  inverse-is-equiv-Synthetic-Category-Theory κ μ ι = pr1

  is-inverse-map-inverse-is-equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D}
    (H : is-equiv-Synthetic-Category-Theory κ μ ι f) →
      is-inverse-Synthetic-Category-Theory κ μ ι f
        ( inverse-is-equiv-Synthetic-Category-Theory κ μ ι H)
  is-inverse-map-inverse-is-equiv-Synthetic-Category-Theory κ μ ι = pr2

  is-section-map-inverse-is-equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D}
    (H : is-equiv-Synthetic-Category-Theory κ μ ι f) →
      is-section-Synthetic-Category-Theory κ μ ι f
        ( inverse-is-equiv-Synthetic-Category-Theory κ μ ι H)
  is-section-map-inverse-is-equiv-Synthetic-Category-Theory κ μ ι H =
    pr1 (is-inverse-map-inverse-is-equiv-Synthetic-Category-Theory κ μ ι H)

  is-retraction-map-inverse-is-equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D}
    (H : is-equiv-Synthetic-Category-Theory κ μ ι f) →
      is-retraction-Synthetic-Category-Theory κ μ ι f
        ( inverse-is-equiv-Synthetic-Category-Theory κ μ ι H)
  is-retraction-map-inverse-is-equiv-Synthetic-Category-Theory κ μ ι H =
    pr2 (is-inverse-map-inverse-is-equiv-Synthetic-Category-Theory κ μ ι H)

  is-section-inverse-is-equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D}
    (H : is-equiv-Synthetic-Category-Theory κ μ ι f) →
      is-section-Synthetic-Category-Theory κ μ ι f
        ( inverse-is-equiv-Synthetic-Category-Theory κ μ ι H)
  is-section-inverse-is-equiv-Synthetic-Category-Theory κ μ ι H =
    is-section-map-inverse-is-equiv-Synthetic-Category-Theory κ μ ι H

  is-retraction-inverse-is-equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D}
    (H : is-equiv-Synthetic-Category-Theory κ μ ι f) →
      is-retraction-Synthetic-Category-Theory κ μ ι f
        ( inverse-is-equiv-Synthetic-Category-Theory κ μ ι H)
  is-retraction-inverse-is-equiv-Synthetic-Category-Theory κ μ ι H =
    is-retraction-map-inverse-is-equiv-Synthetic-Category-Theory κ μ ι H

  section-is-equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D} →
    is-equiv-Synthetic-Category-Theory κ μ ι f →
      section-Synthetic-Category-Theory κ μ ι f
  section-is-equiv-Synthetic-Category-Theory κ μ ι H =
    inverse-is-equiv-Synthetic-Category-Theory κ μ ι H ,
    is-section-map-inverse-is-equiv-Synthetic-Category-Theory κ μ ι H

  retraction-is-equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D} →
    is-equiv-Synthetic-Category-Theory κ μ ι f →
      retraction-Synthetic-Category-Theory κ μ ι f
  retraction-is-equiv-Synthetic-Category-Theory κ μ ι H =
    inverse-is-equiv-Synthetic-Category-Theory κ μ ι H ,
    is-retraction-map-inverse-is-equiv-Synthetic-Category-Theory κ μ ι H
```

A functor f : C → D admits a section and a retraction iff it is an equivalence
(Lemma 1.1.6. in the book.)

```agda
module _
  {l : Level}
  where

  is-biinv-is-equiv-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    {C D : category-Synthetic-Category-Theory κ}
    {f : functor-Synthetic-Category-Theory κ C D} →
    is-equiv-Synthetic-Category-Theory κ μ ι f →
      is-biinv-Synthetic-Category-Theory κ μ ι f
  is-biinv-is-equiv-Synthetic-Category-Theory κ μ ι H =
      section-is-equiv-Synthetic-Category-Theory κ μ ι H ,
      retraction-is-equiv-Synthetic-Category-Theory κ μ ι H


  is-equiv-is-biinv-Synthetic-Category-Theory :
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
    is-biinv-Synthetic-Category-Theory κ μ ι f →
      is-equiv-Synthetic-Category-Theory κ μ ι f
  is-equiv-is-biinv-Synthetic-Category-Theory κ μ ι ν Λ Ρ Χ Α B =
    map-section-Synthetic-Category-Theory κ μ ι
      ( section-is-biinv-Synthetic-Category-Theory κ μ ι B) ,
    is-section-map-section-Synthetic-Category-Theory κ μ ι
      ( section-is-biinv-Synthetic-Category-Theory κ μ ι B) ,
    comp-iso-Synthetic-Category-Theory μ
      ( is-retraction-map-retraction-Synthetic-Category-Theory κ μ ι
        ( retraction-is-biinv-Synthetic-Category-Theory κ μ ι B))
      ( horizontal-comp-iso-Synthetic-Category-Theory Χ
        ( comp-iso-Synthetic-Category-Theory μ
          ( comp-iso-Synthetic-Category-Theory μ
            ( comp-iso-Synthetic-Category-Theory μ
              ( comp-iso-Synthetic-Category-Theory μ
                ( right-unit-law-comp-functor-Synthetic-Category-Theory Ρ
                  ( map-retraction-Synthetic-Category-Theory κ μ ι
                    ( retraction-is-biinv-Synthetic-Category-Theory κ μ ι B)))
                ( horizontal-comp-iso-Synthetic-Category-Theory Χ
                  ( id-iso-Synthetic-Category-Theory ι
                    ( map-retraction-Synthetic-Category-Theory κ μ ι
                      ( retraction-is-biinv-Synthetic-Category-Theory κ μ ι B)))
                  ( is-section-map-section-Synthetic-Category-Theory κ μ ι
                    ( section-is-biinv-Synthetic-Category-Theory κ μ ι B))))
              ( associative-comp-functor-Synthetic-Category-Theory Α
                ( map-retraction-Synthetic-Category-Theory κ μ ι
                  ( retraction-is-biinv-Synthetic-Category-Theory κ μ ι B))
                ( _)
                ( map-section-Synthetic-Category-Theory κ μ ι
                  ( section-is-biinv-Synthetic-Category-Theory κ μ ι B))))
            ( horizontal-comp-iso-Synthetic-Category-Theory Χ
              ( inv-iso-Synthetic-Category-Theory ν
                ( is-retraction-map-retraction-Synthetic-Category-Theory κ μ ι
                  ( retraction-is-biinv-Synthetic-Category-Theory κ μ ι B)))
              ( id-iso-Synthetic-Category-Theory ι
                ( map-section-Synthetic-Category-Theory κ μ ι
                  ( section-is-biinv-Synthetic-Category-Theory κ μ ι B)))))
          ( inv-iso-Synthetic-Category-Theory ν
            ( left-unit-law-comp-functor-Synthetic-Category-Theory Λ
              ( map-section-Synthetic-Category-Theory κ μ ι
                ( section-is-biinv-Synthetic-Category-Theory κ μ ι B)))))
        ( id-iso-Synthetic-Category-Theory ι _))
```

Equivalences are closed under composition (lemma 1.1.8.)

```agda
module _
  {l : Level}
  where

  equiv-comp-equiv-Synthetic-Category-Theory :
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
    is-equiv-Synthetic-Category-Theory κ μ ι f' →
    is-equiv-Synthetic-Category-Theory κ μ ι f →
      is-equiv-Synthetic-Category-Theory κ μ ι
        ( comp-functor-Synthetic-Category-Theory μ f' f)
  equiv-comp-equiv-Synthetic-Category-Theory κ μ ι ν Λ Ρ Χ Α K H =
    ( comp-functor-Synthetic-Category-Theory μ _ _) ,
    ( comp-iso-Synthetic-Category-Theory μ
      ( is-section-map-section-Synthetic-Category-Theory κ μ ι
        ( section-is-equiv-Synthetic-Category-Theory κ μ ι K))
      ( comp-iso-Synthetic-Category-Theory μ
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( right-unit-law-comp-functor-Synthetic-Category-Theory Ρ _)
          ( id-iso-Synthetic-Category-Theory ι
            ( _)))
        ( comp-iso-Synthetic-Category-Theory μ
          ( horizontal-comp-iso-Synthetic-Category-Theory Χ
            ( horizontal-comp-iso-Synthetic-Category-Theory Χ
              ( id-iso-Synthetic-Category-Theory ι _)
              ( is-section-map-section-Synthetic-Category-Theory κ μ ι
                ( section-is-equiv-Synthetic-Category-Theory κ μ ι H)))
            ( id-iso-Synthetic-Category-Theory ι _))
          ( comp-iso-Synthetic-Category-Theory μ
            ( horizontal-comp-iso-Synthetic-Category-Theory Χ
              ( associative-comp-functor-Synthetic-Category-Theory Α _ _ _)
              ( id-iso-Synthetic-Category-Theory ι _))
            ( inv-iso-Synthetic-Category-Theory ν
              ( associative-comp-functor-Synthetic-Category-Theory Α
                ( comp-functor-Synthetic-Category-Theory μ _ _)
                ( _)
                ( _))))))) ,
    comp-iso-Synthetic-Category-Theory μ
      ( is-retraction-map-retraction-Synthetic-Category-Theory κ μ ι
        ( retraction-is-equiv-Synthetic-Category-Theory κ μ ι H))
      ( comp-iso-Synthetic-Category-Theory μ
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( right-unit-law-comp-functor-Synthetic-Category-Theory Ρ _)
          ( id-iso-Synthetic-Category-Theory ι _))
        ( comp-iso-Synthetic-Category-Theory μ
          ( horizontal-comp-iso-Synthetic-Category-Theory Χ
            ( horizontal-comp-iso-Synthetic-Category-Theory Χ
              ( id-iso-Synthetic-Category-Theory ι _)
              ( is-retraction-map-retraction-Synthetic-Category-Theory κ μ ι
                ( retraction-is-equiv-Synthetic-Category-Theory κ μ ι K)))
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
