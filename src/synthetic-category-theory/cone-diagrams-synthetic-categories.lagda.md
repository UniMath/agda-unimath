# Cone diagrams of synthetic categories

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.cone-diagrams-synthetic-categories where
```

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.globular-types

open import synthetic-category-theory.synthetic-categories
open import synthetic-category-theory.cospans-synthetic-categories
```

### Cone diagrams of synthetic categories

A cone diagram over a cospan D--g-->E<--f--C with an apex T is a pair of maps p
: T → C, r : T → D together with a commutative square τ : f∘p ≅ g∘r.

```agda
module _
  {l : Level}
  where

  cone-diagram-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (S : cospan-Synthetic-Category-Theory κ C D E)
    (T : category-Synthetic-Category-Theory κ) → UU l
  cone-diagram-Synthetic-Category-Theory κ μ S T =
    Σ ( functor-Synthetic-Category-Theory
        κ T (right-source-cospan-Synthetic-Category-Theory κ S))
      λ tr →
        Σ ( functor-Synthetic-Category-Theory
            κ T (left-source-cospan-Synthetic-Category-Theory κ S))
          λ tl →
            isomorphism-Synthetic-Category-Theory κ
              ( comp-functor-Synthetic-Category-Theory
                μ ( right-map-cospan-Synthetic-Category-Theory κ S) tr)
              ( comp-functor-Synthetic-Category-Theory
                μ (left-map-cospan-Synthetic-Category-Theory κ S) tl)

  apex-cone-diagram-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (S : cospan-Synthetic-Category-Theory κ C D E)
    (T : category-Synthetic-Category-Theory κ) →
    cone-diagram-Synthetic-Category-Theory κ μ S T →
      category-Synthetic-Category-Theory κ
  apex-cone-diagram-Synthetic-Category-Theory κ μ S T c = T

  left-map-cone-diagram-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (S : cospan-Synthetic-Category-Theory κ C D E)
    (T : category-Synthetic-Category-Theory κ)
    (c : cone-diagram-Synthetic-Category-Theory κ μ S T) →
      functor-Synthetic-Category-Theory κ
        ( apex-cone-diagram-Synthetic-Category-Theory κ μ S T c)
        ( left-source-cospan-Synthetic-Category-Theory κ S)
  left-map-cone-diagram-Synthetic-Category-Theory κ μ S T c = pr1 (pr2 c)

  right-map-cone-diagram-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (S : cospan-Synthetic-Category-Theory κ C D E)
    (T : category-Synthetic-Category-Theory κ)
    (c : cone-diagram-Synthetic-Category-Theory κ μ S T) →
      functor-Synthetic-Category-Theory κ
        ( apex-cone-diagram-Synthetic-Category-Theory κ μ S T c)
        ( right-source-cospan-Synthetic-Category-Theory κ S)
  right-map-cone-diagram-Synthetic-Category-Theory κ μ S T c = pr1 c

  iso-cone-diagram-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (S : cospan-Synthetic-Category-Theory κ C D E)
    (T : category-Synthetic-Category-Theory κ)
    (c : cone-diagram-Synthetic-Category-Theory κ μ S T) →
    isomorphism-Synthetic-Category-Theory κ
      ( comp-functor-Synthetic-Category-Theory μ
        ( right-map-cospan-Synthetic-Category-Theory κ S)
        ( right-map-cone-diagram-Synthetic-Category-Theory κ μ S T c))
      ( comp-functor-Synthetic-Category-Theory μ
        ( left-map-cospan-Synthetic-Category-Theory κ S)
        ( left-map-cone-diagram-Synthetic-Category-Theory κ μ S T c))
  iso-cone-diagram-Synthetic-Category-Theory κ μ S T c = pr2 (pr2 c)

  iso-of-cone-diagrams-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    (Χ : horizontal-composition-Synthetic-Category-Theory κ μ)
    (S : cospan-Synthetic-Category-Theory κ C D E)
    (T : category-Synthetic-Category-Theory κ) →
    cone-diagram-Synthetic-Category-Theory κ μ S T →
    cone-diagram-Synthetic-Category-Theory κ μ S T → UU l
  iso-of-cone-diagrams-Synthetic-Category-Theory κ μ ι Χ S T c c' =
    Σ ( isomorphism-Synthetic-Category-Theory κ
        ( right-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)
        ( right-map-cone-diagram-Synthetic-Category-Theory κ μ S T c'))
      λ φr →
        Σ ( isomorphism-Synthetic-Category-Theory κ
            ( left-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)
            ( left-map-cone-diagram-Synthetic-Category-Theory κ μ S T c'))
          λ φl →
            commuting-square-isomorphisms-Synthetic-Category-Theory κ μ
              ( iso-cone-diagram-Synthetic-Category-Theory κ μ S T c)
                ( horizontal-comp-iso-Synthetic-Category-Theory Χ
                  ( id-iso-Synthetic-Category-Theory ι
                    ( left-map-cospan-Synthetic-Category-Theory κ S))
                  ( φl))
                ( horizontal-comp-iso-Synthetic-Category-Theory Χ
                  ( id-iso-Synthetic-Category-Theory ι
                    ( right-map-cospan-Synthetic-Category-Theory κ S))
                  ( φr))
                ( iso-cone-diagram-Synthetic-Category-Theory κ μ S T c')

  right-map-iso-of-cone-diagrams-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    (Χ : horizontal-composition-Synthetic-Category-Theory κ μ)
    (S : cospan-Synthetic-Category-Theory κ C D E)
    (T : category-Synthetic-Category-Theory κ)
    (c c' : cone-diagram-Synthetic-Category-Theory κ μ S T) →
    (iso-of-cone-diagrams-Synthetic-Category-Theory κ μ ι Χ S T c c') →
    (isomorphism-Synthetic-Category-Theory κ
      ( right-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)
      ( right-map-cone-diagram-Synthetic-Category-Theory κ μ S T c'))
  right-map-iso-of-cone-diagrams-Synthetic-Category-Theory
    κ μ ι Χ S T c c' ϕ = pr1 ϕ

  left-map-iso-of-cone-diagrams-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    (Χ : horizontal-composition-Synthetic-Category-Theory κ μ)
    (S : cospan-Synthetic-Category-Theory κ C D E)
    (T : category-Synthetic-Category-Theory κ)
    (c c' : cone-diagram-Synthetic-Category-Theory κ μ S T) →
    (iso-of-cone-diagrams-Synthetic-Category-Theory κ μ ι Χ S T c c') →
    (isomorphism-Synthetic-Category-Theory κ
      ( left-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)
      ( left-map-cone-diagram-Synthetic-Category-Theory κ μ S T c'))
  left-map-iso-of-cone-diagrams-Synthetic-Category-Theory
    κ μ ι Χ S T c c' ϕ = pr1 (pr2 ϕ)

  isomorphism-iso-of-cone-diagrams-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    (Χ : horizontal-composition-Synthetic-Category-Theory κ μ)
    (S : cospan-Synthetic-Category-Theory κ C D E)
    (T : category-Synthetic-Category-Theory κ)
    (c c' : cone-diagram-Synthetic-Category-Theory κ μ S T) →
    (ϕ : iso-of-cone-diagrams-Synthetic-Category-Theory κ μ ι Χ S T c c') →
    commuting-square-isomorphisms-Synthetic-Category-Theory κ μ
      ( iso-cone-diagram-Synthetic-Category-Theory κ μ S T c)
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( id-iso-Synthetic-Category-Theory ι
            ( left-map-cospan-Synthetic-Category-Theory κ S))
          ( left-map-iso-of-cone-diagrams-Synthetic-Category-Theory
            κ μ ι Χ S T c c' ϕ))
      ( horizontal-comp-iso-Synthetic-Category-Theory Χ
        ( id-iso-Synthetic-Category-Theory ι
          ( right-map-cospan-Synthetic-Category-Theory κ S))
        ( right-map-iso-of-cone-diagrams-Synthetic-Category-Theory
          κ μ ι Χ S T c c' ϕ))
      ( iso-cone-diagram-Synthetic-Category-Theory κ μ S T c')
  isomorphism-iso-of-cone-diagrams-Synthetic-Category-Theory
    κ μ ι Χ S T c c' ϕ = pr2 (pr2 ϕ)

  iso-of-isos-of-cone-diagrams-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    (ν : inverse-Synthetic-Category-Theory κ μ ι)
    (Χ : horizontal-composition-Synthetic-Category-Theory κ μ)
    (Μ : preserves-isomorphism-horizontal-composition-Synthetic-Category-Theory κ ι μ Χ)
    (S : cospan-Synthetic-Category-Theory κ C D E)
    (T : category-Synthetic-Category-Theory κ)
    (c c' : cone-diagram-Synthetic-Category-Theory κ μ S T)
    (ϕ ψ : iso-of-cone-diagrams-Synthetic-Category-Theory κ μ ι Χ S T c c') →
      UU l
  iso-of-isos-of-cone-diagrams-Synthetic-Category-Theory
    κ μ ι ν Χ Μ S T c c' ϕ ψ =
    Σ ( isomorphism-Synthetic-Category-Theory
        ( functor-globular-type-Synthetic-Category-Theory κ
          ( T)
          ( right-source-cospan-Synthetic-Category-Theory κ S))
        ( right-map-iso-of-cone-diagrams-Synthetic-Category-Theory
          κ μ ι Χ S T c c' ϕ)
        ( right-map-iso-of-cone-diagrams-Synthetic-Category-Theory
          κ μ ι Χ S T c c' ψ))
      λ α →
      Σ ( isomorphism-Synthetic-Category-Theory
          ( functor-globular-type-Synthetic-Category-Theory κ
            ( T)
          ( left-source-cospan-Synthetic-Category-Theory κ S))
        ( left-map-iso-of-cone-diagrams-Synthetic-Category-Theory
          κ μ ι Χ S T c c' ϕ)
        ( left-map-iso-of-cone-diagrams-Synthetic-Category-Theory
          κ μ ι Χ S T c c' ψ))
        λ β →
        isomorphism-Synthetic-Category-Theory
          ( functor-globular-type-Synthetic-Category-Theory
            ( functor-globular-type-Synthetic-Category-Theory κ
              ( T)
              ( target-cospan-Synthetic-Category-Theory κ S))
            ( comp-functor-Synthetic-Category-Theory μ
              ( right-map-cospan-Synthetic-Category-Theory κ S)
              ( right-map-cone-diagram-Synthetic-Category-Theory
                κ μ S T c))
            ( comp-functor-Synthetic-Category-Theory μ
              ( left-map-cospan-Synthetic-Category-Theory κ S)
              ( left-map-cone-diagram-Synthetic-Category-Theory
                κ μ S T c')))
          ( comp-iso-Synthetic-Category-Theory
            ( composition-isomorphism-Synthetic-Category-Theory μ)
            ( horizontal-comp-iso-Synthetic-Category-Theory
              ( horizontal-composition-isomorphism-Synthetic-Category-Theory Χ)
              ( id-iso-Synthetic-Category-Theory
                ( identity-isomorphism-Synthetic-Category-Theory ι)
                ( iso-cone-diagram-Synthetic-Category-Theory κ μ S T c'))
              ( preserves-isomorphism-horizontal-comp-iso-Synthetic-Category-Theory Μ
                ( α)
                ( id-iso-Synthetic-Category-Theory
                  ( identity-isomorphism-Synthetic-Category-Theory ι)
                  ( id-iso-Synthetic-Category-Theory ι
                    ( right-map-cospan-Synthetic-Category-Theory κ S)))))
            ( comp-iso-Synthetic-Category-Theory
              ( composition-isomorphism-Synthetic-Category-Theory μ)
              ( isomorphism-iso-of-cone-diagrams-Synthetic-Category-Theory
                κ μ ι Χ S T c c' ϕ)
              ( horizontal-comp-iso-Synthetic-Category-Theory
                ( horizontal-composition-isomorphism-Synthetic-Category-Theory Χ)
                ( preserves-isomorphism-horizontal-comp-iso-Synthetic-Category-Theory Μ
                  ( inv-iso-Synthetic-Category-Theory
                    ( inverse-isomorphism-Synthetic-Category-Theory ν)
                    ( β))
                  ( id-iso-Synthetic-Category-Theory
                    ( identity-isomorphism-Synthetic-Category-Theory ι)
                    ( id-iso-Synthetic-Category-Theory ι
                      ( left-map-cospan-Synthetic-Category-Theory κ S))))
                ( id-iso-Synthetic-Category-Theory
                  ( identity-isomorphism-Synthetic-Category-Theory ι)
                  ( iso-cone-diagram-Synthetic-Category-Theory
                    κ μ S T c)))))
          ( isomorphism-iso-of-cone-diagrams-Synthetic-Category-Theory
            κ μ ι Χ S T c c' ψ)
```

Given a cone over S with apex T and a functor s : R → T we get and induced cone
over S with apex R.

```agda
module _
  {l : Level}
  where

  induced-cone-diagram-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    (ν : inverse-Synthetic-Category-Theory κ μ ι)
    (Χ : horizontal-composition-Synthetic-Category-Theory κ μ)
    (Α : associative-composition-Synthetic-Category-Theory κ μ)
    (S : cospan-Synthetic-Category-Theory κ C D E)
    (T : category-Synthetic-Category-Theory κ)
    (c : cone-diagram-Synthetic-Category-Theory κ μ S T)
    (R : category-Synthetic-Category-Theory κ)
    (s : functor-Synthetic-Category-Theory κ R T) →
      cone-diagram-Synthetic-Category-Theory κ μ S R
  induced-cone-diagram-Synthetic-Category-Theory κ μ ι ν Χ Α S T c R s =
    comp-functor-Synthetic-Category-Theory μ
      ( right-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)
      ( s) ,
    comp-functor-Synthetic-Category-Theory μ
      ( left-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)
      ( s) ,
    comp-iso-Synthetic-Category-Theory μ
      ( associative-comp-functor-Synthetic-Category-Theory Α
        ( left-map-cospan-Synthetic-Category-Theory κ S)
        ( left-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)
        ( s))
      ( comp-iso-Synthetic-Category-Theory μ
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( iso-cone-diagram-Synthetic-Category-Theory κ μ S T c)
          ( id-iso-Synthetic-Category-Theory ι s))
        ( inv-iso-Synthetic-Category-Theory ν
          ( associative-comp-functor-Synthetic-Category-Theory Α
            ( right-map-cospan-Synthetic-Category-Theory κ S)
            ( right-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)
            ( s))))
```

Given a cone over S with apex T and two functors s, t : R → T together with an
isomorphism between s and t, we get an isomorphism of cone diagrams between the
cone diagrams induced by s and t.

```agda
module _
  {l : Level}
  where

  induced-iso-cone-diagram-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    (ν : inverse-Synthetic-Category-Theory κ μ ι)
    (Α : associative-composition-Synthetic-Category-Theory κ μ)
    (Χ : horizontal-composition-Synthetic-Category-Theory κ μ)
    (Λ : left-unit-law-composition-Synthetic-Category-Theory κ ι μ)
    (Ρ : right-unit-law-composition-Synthetic-Category-Theory κ ι μ)
    (Ξ : preserves-associativity-composition-horizontal-composition-Synthetic-Category-Theory κ μ Α Χ)
    (I : interchange-composition-Synthetic-Category-Theory κ μ Χ)
    (M : preserves-isomorphism-horizontal-composition-Synthetic-Category-Theory κ ι μ Χ)
    (N : preserves-identity-horizontal-composition-Synthetic-Category-Theory κ ι μ Χ)
    (S : cospan-Synthetic-Category-Theory κ C D E)
    (T : category-Synthetic-Category-Theory κ)
    (c : cone-diagram-Synthetic-Category-Theory κ μ S T)
    (R : category-Synthetic-Category-Theory κ)
    (s t : functor-Synthetic-Category-Theory κ R T) →
    isomorphism-Synthetic-Category-Theory κ s t →
      iso-of-cone-diagrams-Synthetic-Category-Theory κ μ ι Χ S R
        ( induced-cone-diagram-Synthetic-Category-Theory κ μ ι ν Χ Α S T c R s)
        ( induced-cone-diagram-Synthetic-Category-Theory κ μ ι ν Χ Α S T c R t)
  induced-iso-cone-diagram-Synthetic-Category-Theory
    κ μ ι ν Α Χ Λ Ρ Ξ I M N S T c R s t α =
    horizontal-comp-iso-Synthetic-Category-Theory Χ
      ( id-iso-Synthetic-Category-Theory ι
        ( right-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)) α ,
    horizontal-comp-iso-Synthetic-Category-Theory Χ
      ( id-iso-Synthetic-Category-Theory ι
        ( left-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)) α ,
    pasting-commuting-squares-isomorphisms-Synthetic-Category-Theory κ μ ι ν Α Χ
      ( comp-iso-Synthetic-Category-Theory μ
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( iso-cone-diagram-Synthetic-Category-Theory κ μ S T c)
          ( id-iso-Synthetic-Category-Theory ι
            ( s)))
        ( inv-iso-Synthetic-Category-Theory ν
          ( associative-comp-functor-Synthetic-Category-Theory Α
            ( right-map-cospan-Synthetic-Category-Theory κ S)
            ( right-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)
            ( s))))
      ( associative-comp-functor-Synthetic-Category-Theory Α
        ( left-map-cospan-Synthetic-Category-Theory κ S)
        ( left-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)
        ( s))
      ( horizontal-comp-iso-Synthetic-Category-Theory Χ
        ( id-iso-Synthetic-Category-Theory ι
          ( left-map-cospan-Synthetic-Category-Theory κ S))
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( id-iso-Synthetic-Category-Theory ι
            ( left-map-cone-diagram-Synthetic-Category-Theory κ μ S T c))
          ( α)))
      ( horizontal-comp-iso-Synthetic-Category-Theory Χ
        ( id-iso-Synthetic-Category-Theory ι
          ( right-map-cospan-Synthetic-Category-Theory κ S))
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( id-iso-Synthetic-Category-Theory ι
            ( right-map-cone-diagram-Synthetic-Category-Theory κ μ S T c))
          ( α)))
      ( comp-iso-Synthetic-Category-Theory μ
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( iso-cone-diagram-Synthetic-Category-Theory κ μ S T c)
          ( id-iso-Synthetic-Category-Theory ι t))
        ( inv-iso-Synthetic-Category-Theory ν
          ( associative-comp-functor-Synthetic-Category-Theory Α
            ( right-map-cospan-Synthetic-Category-Theory κ S)
            ( right-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)
            ( t))))
      ( associative-comp-functor-Synthetic-Category-Theory Α
        ( left-map-cospan-Synthetic-Category-Theory κ S)
        ( left-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)
        ( t))
      ( horizontal-comp-iso-Synthetic-Category-Theory Χ
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( id-iso-Synthetic-Category-Theory ι
            (left-map-cospan-Synthetic-Category-Theory κ S))
          ( id-iso-Synthetic-Category-Theory ι
            ( left-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)))
        ( α))
      ( pasting-commuting-squares-isomorphisms-Synthetic-Category-Theory
        κ μ ι ν Α Χ
        ( inv-iso-Synthetic-Category-Theory ν
          ( associative-comp-functor-Synthetic-Category-Theory Α
            ( right-map-cospan-Synthetic-Category-Theory κ S)
            ( right-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)
            ( s)))
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( iso-cone-diagram-Synthetic-Category-Theory κ μ S T c)
          ( id-iso-Synthetic-Category-Theory ι s))
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( horizontal-comp-iso-Synthetic-Category-Theory Χ
            ( id-iso-Synthetic-Category-Theory ι
              ( left-map-cospan-Synthetic-Category-Theory κ S))
            ( id-iso-Synthetic-Category-Theory ι
              ( left-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)))
          ( α))
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( id-iso-Synthetic-Category-Theory ι
            ( right-map-cospan-Synthetic-Category-Theory κ S))
          ( horizontal-comp-iso-Synthetic-Category-Theory Χ
            ( id-iso-Synthetic-Category-Theory ι
              ( right-map-cone-diagram-Synthetic-Category-Theory κ μ S T c))
            ( α)))
        ( inv-iso-Synthetic-Category-Theory ν
          ( associative-comp-functor-Synthetic-Category-Theory Α
            ( right-map-cospan-Synthetic-Category-Theory κ S)
            ( right-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)
            ( t)))
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( iso-cone-diagram-Synthetic-Category-Theory κ μ S T c)
          ( id-iso-Synthetic-Category-Theory ι t))
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( horizontal-comp-iso-Synthetic-Category-Theory Χ
            ( id-iso-Synthetic-Category-Theory ι
              ( right-map-cospan-Synthetic-Category-Theory κ S))
            ( id-iso-Synthetic-Category-Theory ι
              ( right-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)))
          ( α))
        ( preserves-associativity-comp-functor-horizontal-comp-iso-inv-Synthetic-Category-Theory
          κ μ ι ν Α Χ Λ Ρ Ξ
          ( right-map-cospan-Synthetic-Category-Theory κ S)
          ( right-map-cospan-Synthetic-Category-Theory κ S)
          ( right-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)
          ( right-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)
          s t
          ( id-iso-Synthetic-Category-Theory ι
            ( right-map-cospan-Synthetic-Category-Theory κ S))
          ( id-iso-Synthetic-Category-Theory ι
            ( right-map-cone-diagram-Synthetic-Category-Theory κ μ S T c))
          ( α))
        ( comp-iso-Synthetic-Category-Theory
          ( composition-isomorphism-Synthetic-Category-Theory μ)
          ( interchange-comp-functor-Synthetic-Category-Theory I
            ( iso-cone-diagram-Synthetic-Category-Theory κ μ S T c)
            ( horizontal-comp-iso-Synthetic-Category-Theory Χ
              ( id-iso-Synthetic-Category-Theory ι
                ( right-map-cospan-Synthetic-Category-Theory κ S))
              ( id-iso-Synthetic-Category-Theory ι
                ( right-map-cone-diagram-Synthetic-Category-Theory κ μ S T c)))
            ( id-iso-Synthetic-Category-Theory ι t)
            ( α))
          ( comp-iso-Synthetic-Category-Theory
            ( composition-isomorphism-Synthetic-Category-Theory μ)
            ( preserves-isomorphism-horizontal-comp-iso-Synthetic-Category-Theory M
              ( inv-iso-Synthetic-Category-Theory
                ( inverse-isomorphism-Synthetic-Category-Theory ν)
                ( left-unit-law-comp-functor-Synthetic-Category-Theory
                  ( left-unit-law-composition-isomorphism-Synthetic-Category-Theory Λ)
                  ( α)))
              ( comp-iso-Synthetic-Category-Theory
                ( composition-isomorphism-Synthetic-Category-Theory μ)
                ( horizontal-comp-iso-Synthetic-Category-Theory
                  ( horizontal-composition-isomorphism-Synthetic-Category-Theory Χ)
                  ( id-iso-Synthetic-Category-Theory
                    ( identity-isomorphism-Synthetic-Category-Theory ι)
                    ( iso-cone-diagram-Synthetic-Category-Theory κ μ S T c))
                  ( inv-iso-Synthetic-Category-Theory
                    ( inverse-isomorphism-Synthetic-Category-Theory ν)
                    ( preserves-identity-horizontal-comp-iso-Synthetic-Category-Theory N)))
                ( inv-iso-Synthetic-Category-Theory
                  ( inverse-isomorphism-Synthetic-Category-Theory ν)
                  ( right-unit-law-comp-functor-Synthetic-Category-Theory
                    ( right-unit-law-composition-isomorphism-Synthetic-Category-Theory Ρ)
                    ( iso-cone-diagram-Synthetic-Category-Theory κ μ S T c)))))
            ( comp-iso-Synthetic-Category-Theory
              ( composition-isomorphism-Synthetic-Category-Theory μ)
              ( preserves-isomorphism-horizontal-comp-iso-Synthetic-Category-Theory M
                ( right-unit-law-comp-functor-Synthetic-Category-Theory
                  ( right-unit-law-composition-isomorphism-Synthetic-Category-Theory Ρ)
                  ( α))
                ( comp-iso-Synthetic-Category-Theory
                  ( composition-isomorphism-Synthetic-Category-Theory μ)
                  ( left-unit-law-comp-functor-Synthetic-Category-Theory
                    ( left-unit-law-composition-isomorphism-Synthetic-Category-Theory Λ)
                    ( iso-cone-diagram-Synthetic-Category-Theory κ μ S T c))
                  ( horizontal-comp-iso-Synthetic-Category-Theory
                    ( horizontal-composition-isomorphism-Synthetic-Category-Theory Χ)
                    ( preserves-identity-horizontal-comp-iso-Synthetic-Category-Theory N)
                    ( id-iso-Synthetic-Category-Theory
                      ( identity-isomorphism-Synthetic-Category-Theory ι)
                      ( iso-cone-diagram-Synthetic-Category-Theory κ μ S T c)))))
                  ( inv-iso-Synthetic-Category-Theory
                    ( inverse-isomorphism-Synthetic-Category-Theory ν)
                    ( interchange-comp-functor-Synthetic-Category-Theory I
                      ( horizontal-comp-iso-Synthetic-Category-Theory Χ
                        ( id-iso-Synthetic-Category-Theory ι
                          ( left-map-cospan-Synthetic-Category-Theory κ S))
                        ( id-iso-Synthetic-Category-Theory ι
                          ( left-map-cone-diagram-Synthetic-Category-Theory
                            κ μ S T c)))
                      ( iso-cone-diagram-Synthetic-Category-Theory κ μ S T c)
                      ( α)
                      ( id-iso-Synthetic-Category-Theory ι s)))))))
      ( preserves-associativity-comp-functor-horizontal-comp-iso-Synthetic-Category-Theory
        ( Ξ)
        ( id-iso-Synthetic-Category-Theory ι
          ( left-map-cospan-Synthetic-Category-Theory κ S))
        ( id-iso-Synthetic-Category-Theory ι
          ( left-map-cone-diagram-Synthetic-Category-Theory κ μ S T c))
        ( α))
```
