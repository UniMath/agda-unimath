# Cone diagrams of synthetic categories

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.cone-diagrams-synthetic-categories where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.globular-types

open import synthetic-category-theory.cospans-synthetic-categories
open import synthetic-category-theory.synthetic-categories
```

</details>

## Idea

Consider a [cospan](synthetic-category-theory.cospans-synthetic-categories.md) S
= D --g--> E <--f-- C of
[synthetic categories](synthetic-category-theory.synthetic-categories.md) and
let T be a synthetic category. A
{{#concept "cone diagram" Disambiguation="Synthetic categories}} over S with an
apex T is a pair of functors p : T → C and r : T → D that assemble into a
commutative square of the form:

```text
T --p--> C
|        |
r   τ⇙   f
|        |
v        v
D --g--> E.
```

## Definition

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
      ( λ tr →
        Σ ( functor-Synthetic-Category-Theory
            κ T (left-source-cospan-Synthetic-Category-Theory κ S))
          ( λ tl →
            isomorphism-Synthetic-Category-Theory κ
              ( comp-functor-Synthetic-Category-Theory μ
                ( right-functor-cospan-Synthetic-Category-Theory κ S) tr)
              ( comp-functor-Synthetic-Category-Theory μ
                ( left-functor-cospan-Synthetic-Category-Theory κ S) tl)))
```

### The components of a cospan of synthetic categories

```agda
  apex-cone-diagram-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    {S : cospan-Synthetic-Category-Theory κ C D E}
    {T : category-Synthetic-Category-Theory κ} →
    cone-diagram-Synthetic-Category-Theory κ μ S T →
    category-Synthetic-Category-Theory κ
  apex-cone-diagram-Synthetic-Category-Theory κ μ {T = T} c = T

  left-functor-cone-diagram-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    {S : cospan-Synthetic-Category-Theory κ C D E}
    {T : category-Synthetic-Category-Theory κ}
    (c : cone-diagram-Synthetic-Category-Theory κ μ S T) →
    functor-Synthetic-Category-Theory κ
      ( apex-cone-diagram-Synthetic-Category-Theory κ μ c)
      ( left-source-cospan-Synthetic-Category-Theory κ S)
  left-functor-cone-diagram-Synthetic-Category-Theory κ μ c = pr1 (pr2 c)

  right-functor-cone-diagram-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    {S : cospan-Synthetic-Category-Theory κ C D E}
    {T : category-Synthetic-Category-Theory κ}
    (c : cone-diagram-Synthetic-Category-Theory κ μ S T) →
    functor-Synthetic-Category-Theory κ
      ( apex-cone-diagram-Synthetic-Category-Theory κ μ c)
      ( right-source-cospan-Synthetic-Category-Theory κ S)
  right-functor-cone-diagram-Synthetic-Category-Theory κ μ c = pr1 c

  iso-cone-diagram-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    {S : cospan-Synthetic-Category-Theory κ C D E}
    {T : category-Synthetic-Category-Theory κ}
    (c : cone-diagram-Synthetic-Category-Theory κ μ S T) →
    isomorphism-Synthetic-Category-Theory κ
      ( comp-functor-Synthetic-Category-Theory μ
        ( right-functor-cospan-Synthetic-Category-Theory κ S)
        ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ c))
      ( comp-functor-Synthetic-Category-Theory μ
        ( left-functor-cospan-Synthetic-Category-Theory κ S)
        ( left-functor-cone-diagram-Synthetic-Category-Theory κ μ c))
  iso-cone-diagram-Synthetic-Category-Theory κ μ c = pr2 (pr2 c)
```

### Isomorphisms of cone diagrams

An isomorphism between cone diagrams c = (tl, tr, τ) and c' = (tl', tr', τ') is
a pair of natural isomorphisms φl : tl ≅ tl' and φr : tr ≅ tr' together with an
isomorphism of natural isomorphisms H : τ ≅ τ'.

```agda
  iso-of-cone-diagrams-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    (Χ : horizontal-composition-Synthetic-Category-Theory κ μ)
    {S : cospan-Synthetic-Category-Theory κ C D E}
    {T : category-Synthetic-Category-Theory κ} →
    cone-diagram-Synthetic-Category-Theory κ μ S T →
    cone-diagram-Synthetic-Category-Theory κ μ S T → UU l
  iso-of-cone-diagrams-Synthetic-Category-Theory κ μ ι Χ {S = S} c c' =
    Σ ( isomorphism-Synthetic-Category-Theory κ
        ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ c)
        ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ c'))
      ( λ φr →
        Σ ( isomorphism-Synthetic-Category-Theory κ
            ( left-functor-cone-diagram-Synthetic-Category-Theory κ μ c)
            ( left-functor-cone-diagram-Synthetic-Category-Theory κ μ c'))
          ( λ φl →
            commuting-square-isomorphisms-Synthetic-Category-Theory κ μ
              ( iso-cone-diagram-Synthetic-Category-Theory κ μ c)
                ( horizontal-comp-iso-Synthetic-Category-Theory Χ
                  ( id-iso-Synthetic-Category-Theory ι
                    ( left-functor-cospan-Synthetic-Category-Theory κ S))
                  ( φl))
                ( horizontal-comp-iso-Synthetic-Category-Theory Χ
                  ( id-iso-Synthetic-Category-Theory ι
                    ( right-functor-cospan-Synthetic-Category-Theory κ S))
                  ( φr))
                ( iso-cone-diagram-Synthetic-Category-Theory κ μ c')))
```

### The components of an isomorphism of cone diagrams

```agda
  right-functor-iso-of-cone-diagrams-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    (Χ : horizontal-composition-Synthetic-Category-Theory κ μ)
    {S : cospan-Synthetic-Category-Theory κ C D E}
    {T : category-Synthetic-Category-Theory κ}
    {c c' : cone-diagram-Synthetic-Category-Theory κ μ S T} →
    (iso-of-cone-diagrams-Synthetic-Category-Theory κ μ ι Χ c c') →
    isomorphism-Synthetic-Category-Theory κ
      ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ c)
      ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ c')
  right-functor-iso-of-cone-diagrams-Synthetic-Category-Theory
    κ μ ι Χ = pr1

  left-functor-iso-of-cone-diagrams-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    (Χ : horizontal-composition-Synthetic-Category-Theory κ μ)
    {S : cospan-Synthetic-Category-Theory κ C D E}
    {T : category-Synthetic-Category-Theory κ}
    {c c' : cone-diagram-Synthetic-Category-Theory κ μ S T} →
    (iso-of-cone-diagrams-Synthetic-Category-Theory κ μ ι Χ c c') →
    isomorphism-Synthetic-Category-Theory κ
      ( left-functor-cone-diagram-Synthetic-Category-Theory κ μ c)
      ( left-functor-cone-diagram-Synthetic-Category-Theory κ μ c')
  left-functor-iso-of-cone-diagrams-Synthetic-Category-Theory
    κ μ ι Χ ϕ = pr1 (pr2 ϕ)

  isomorphism-iso-of-cone-diagrams-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    (Χ : horizontal-composition-Synthetic-Category-Theory κ μ)
    {S : cospan-Synthetic-Category-Theory κ C D E}
    {T : category-Synthetic-Category-Theory κ}
    {c c' : cone-diagram-Synthetic-Category-Theory κ μ S T} →
    (ϕ : iso-of-cone-diagrams-Synthetic-Category-Theory κ μ ι Χ c c') →
    commuting-square-isomorphisms-Synthetic-Category-Theory κ μ
      ( iso-cone-diagram-Synthetic-Category-Theory κ μ c)
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( id-iso-Synthetic-Category-Theory ι
            ( left-functor-cospan-Synthetic-Category-Theory κ S))
          ( left-functor-iso-of-cone-diagrams-Synthetic-Category-Theory
            κ μ ι Χ ϕ))
      ( horizontal-comp-iso-Synthetic-Category-Theory Χ
        ( id-iso-Synthetic-Category-Theory ι
          ( right-functor-cospan-Synthetic-Category-Theory κ S))
        ( right-functor-iso-of-cone-diagrams-Synthetic-Category-Theory
          κ μ ι Χ ϕ))
      ( iso-cone-diagram-Synthetic-Category-Theory κ μ c')
  isomorphism-iso-of-cone-diagrams-Synthetic-Category-Theory
    κ μ ι Χ ϕ = pr2 (pr2 ϕ)
```

## Isomorphisms of isomorphisms of cone diagrams

If ϕ = (φl, φr, H) and Ψ = (ψl, ψr, K) are two isomorphisms between cone
diagrams c and c', an isomorphism between them is a pair of isomorphisms φl ≅ ψl
and φr ≅ ψr under which H becomes isomorphic to K.

```agda
  iso-of-isos-of-cone-diagrams-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l)
    {C D E : category-Synthetic-Category-Theory κ}
    (μ : composition-Synthetic-Category-Theory κ)
    (ι : identity-Synthetic-Category-Theory κ)
    (ν : inverse-Synthetic-Category-Theory κ μ ι)
    (Χ : horizontal-composition-Synthetic-Category-Theory κ μ)
    (Μ :
      preserves-isomorphism-horizontal-composition-Synthetic-Category-Theory
        κ ι μ Χ)
    {S : cospan-Synthetic-Category-Theory κ C D E}
    {T : category-Synthetic-Category-Theory κ}
    {c c' : cone-diagram-Synthetic-Category-Theory κ μ S T}
    (ϕ ψ : iso-of-cone-diagrams-Synthetic-Category-Theory κ μ ι Χ c c') → UU l
  iso-of-isos-of-cone-diagrams-Synthetic-Category-Theory
    κ μ ι ν Χ Μ {S = S} {c = c} {c' = c'} ϕ ψ =
    Σ ( isomorphism-Synthetic-Category-Theory
        ( functor-globular-type-Synthetic-Category-Theory κ
          ( _)
          ( right-source-cospan-Synthetic-Category-Theory κ S))
        ( right-functor-iso-of-cone-diagrams-Synthetic-Category-Theory
          κ μ ι Χ ϕ)
        ( right-functor-iso-of-cone-diagrams-Synthetic-Category-Theory
          κ μ ι Χ ψ))
      ( λ α →
        Σ ( isomorphism-Synthetic-Category-Theory
            ( functor-globular-type-Synthetic-Category-Theory κ
              ( _)
              ( left-source-cospan-Synthetic-Category-Theory κ S))
            ( left-functor-iso-of-cone-diagrams-Synthetic-Category-Theory
              κ μ ι Χ ϕ)
            ( left-functor-iso-of-cone-diagrams-Synthetic-Category-Theory
              κ μ ι Χ ψ))
          ( λ β →
            isomorphism-Synthetic-Category-Theory
              ( functor-globular-type-Synthetic-Category-Theory
                ( functor-globular-type-Synthetic-Category-Theory κ
                  ( _)
                  ( target-cospan-Synthetic-Category-Theory κ S))
                ( comp-functor-Synthetic-Category-Theory μ
                  ( right-functor-cospan-Synthetic-Category-Theory κ S)
                  ( right-functor-cone-diagram-Synthetic-Category-Theory
                    κ μ c))
                ( comp-functor-Synthetic-Category-Theory μ
                  ( left-functor-cospan-Synthetic-Category-Theory κ S)
                  ( left-functor-cone-diagram-Synthetic-Category-Theory
                    κ μ c')))
              ( comp-iso-Synthetic-Category-Theory
                ( composition-isomorphism-Synthetic-Category-Theory μ)
                ( horizontal-comp-iso-Synthetic-Category-Theory
                  ( horizontal-composition-isomorphism-Synthetic-Category-Theory
                    Χ)
                  ( id-iso-Synthetic-Category-Theory
                    ( identity-isomorphism-Synthetic-Category-Theory ι)
                    ( iso-cone-diagram-Synthetic-Category-Theory κ μ c'))
                  ( preserves-isomorphism-horizontal-comp-iso-Synthetic-Category-Theory
                    ( Μ)
                    ( α)
                    ( id-iso-Synthetic-Category-Theory
                      ( identity-isomorphism-Synthetic-Category-Theory ι)
                      ( id-iso-Synthetic-Category-Theory ι
                        ( right-functor-cospan-Synthetic-Category-Theory
                          κ S)))))
                ( comp-iso-Synthetic-Category-Theory
                  ( composition-isomorphism-Synthetic-Category-Theory μ)
                  ( isomorphism-iso-of-cone-diagrams-Synthetic-Category-Theory
                    κ μ ι Χ ϕ)
                  ( horizontal-comp-iso-Synthetic-Category-Theory
                    ( horizontal-composition-isomorphism-Synthetic-Category-Theory
                      Χ)
                    ( preserves-isomorphism-horizontal-comp-iso-Synthetic-Category-Theory
                      ( Μ)
                      ( inv-iso-Synthetic-Category-Theory
                        ( inverse-isomorphism-Synthetic-Category-Theory ν)
                        ( β))
                      ( id-iso-Synthetic-Category-Theory
                        ( identity-isomorphism-Synthetic-Category-Theory ι)
                        ( id-iso-Synthetic-Category-Theory ι
                          ( left-functor-cospan-Synthetic-Category-Theory
                            κ S))))
                    ( id-iso-Synthetic-Category-Theory
                      ( identity-isomorphism-Synthetic-Category-Theory ι)
                      ( iso-cone-diagram-Synthetic-Category-Theory
                        κ μ c)))))
              ( isomorphism-iso-of-cone-diagrams-Synthetic-Category-Theory
                κ μ ι Χ ψ)))
```

## Induced cones

Given a cone c = (tl, tr, τ) over S with apex T and a functor s : R → T we
construct an induced cone over S with apex R, defined as s*(c) = (tl∘s, tr∘s,
τ*idₛ).

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
    {T : category-Synthetic-Category-Theory κ}
    (c : cone-diagram-Synthetic-Category-Theory κ μ S T)
    {R : category-Synthetic-Category-Theory κ}
    (s : functor-Synthetic-Category-Theory κ R T) →
      cone-diagram-Synthetic-Category-Theory κ μ S R
  induced-cone-diagram-Synthetic-Category-Theory κ μ ι ν Χ Α S c s =
    comp-functor-Synthetic-Category-Theory μ
      ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ c)
      ( s) ,
    comp-functor-Synthetic-Category-Theory μ
      ( left-functor-cone-diagram-Synthetic-Category-Theory κ μ c)
      ( s) ,
    comp-iso-Synthetic-Category-Theory μ
      ( associative-comp-functor-Synthetic-Category-Theory Α
        ( left-functor-cospan-Synthetic-Category-Theory κ S)
        ( left-functor-cone-diagram-Synthetic-Category-Theory κ μ c)
        ( s))
      ( comp-iso-Synthetic-Category-Theory μ
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( iso-cone-diagram-Synthetic-Category-Theory κ μ c)
          ( id-iso-Synthetic-Category-Theory ι s))
        ( inv-iso-Synthetic-Category-Theory ν
          ( associative-comp-functor-Synthetic-Category-Theory Α
            ( right-functor-cospan-Synthetic-Category-Theory κ S)
            ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ c)
            ( s))))
```

## Induced isomorphisms of cone diagrams

Given a cone over S with apex T and two functors s, t : R → T together with an
isomorphism s ≅ t, we construct an isomorphism of cone diagrams between s*(c)
and t*(c).

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
    (Ξ :
      preserves-associativity-composition-horizontal-composition-Synthetic-Category-Theory
        κ μ Α Χ)
    (I : interchange-composition-Synthetic-Category-Theory κ μ Χ)
    (Μ :
      preserves-isomorphism-horizontal-composition-Synthetic-Category-Theory
        κ ι μ Χ)
    (N :
      preserves-identity-horizontal-composition-Synthetic-Category-Theory
        κ ι μ Χ)
    (S : cospan-Synthetic-Category-Theory κ C D E)
    {T : category-Synthetic-Category-Theory κ}
    (c : cone-diagram-Synthetic-Category-Theory κ μ S T)
    {R : category-Synthetic-Category-Theory κ}
    (s t : functor-Synthetic-Category-Theory κ R T) →
    isomorphism-Synthetic-Category-Theory κ s t →
      iso-of-cone-diagrams-Synthetic-Category-Theory κ μ ι Χ
        ( induced-cone-diagram-Synthetic-Category-Theory κ μ ι ν Χ Α S c s)
        ( induced-cone-diagram-Synthetic-Category-Theory κ μ ι ν Χ Α S c t)
  induced-iso-cone-diagram-Synthetic-Category-Theory
    κ μ ι ν Α Χ Λ Ρ Ξ I M N S c s t α =
    horizontal-comp-iso-Synthetic-Category-Theory Χ
      ( id-iso-Synthetic-Category-Theory ι
        ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ c)) α ,
    horizontal-comp-iso-Synthetic-Category-Theory Χ
      ( id-iso-Synthetic-Category-Theory ι
        ( left-functor-cone-diagram-Synthetic-Category-Theory κ μ c)) α ,
    pasting-commuting-squares-isomorphisms-Synthetic-Category-Theory κ μ ι ν Α Χ
      ( comp-iso-Synthetic-Category-Theory μ
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( iso-cone-diagram-Synthetic-Category-Theory κ μ c)
          ( id-iso-Synthetic-Category-Theory ι
            ( s)))
        ( inv-iso-Synthetic-Category-Theory ν
          ( associative-comp-functor-Synthetic-Category-Theory Α
            ( right-functor-cospan-Synthetic-Category-Theory κ S)
            ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ c)
            ( s))))
      ( associative-comp-functor-Synthetic-Category-Theory Α
        ( left-functor-cospan-Synthetic-Category-Theory κ S)
        ( left-functor-cone-diagram-Synthetic-Category-Theory κ μ c)
        ( s))
      ( horizontal-comp-iso-Synthetic-Category-Theory Χ
        ( id-iso-Synthetic-Category-Theory ι
          ( left-functor-cospan-Synthetic-Category-Theory κ S))
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( id-iso-Synthetic-Category-Theory ι
            ( left-functor-cone-diagram-Synthetic-Category-Theory κ μ c))
          ( α)))
      ( horizontal-comp-iso-Synthetic-Category-Theory Χ
        ( id-iso-Synthetic-Category-Theory ι
          ( right-functor-cospan-Synthetic-Category-Theory κ S))
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( id-iso-Synthetic-Category-Theory ι
            ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ c))
          ( α)))
      ( comp-iso-Synthetic-Category-Theory μ
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( iso-cone-diagram-Synthetic-Category-Theory κ μ c)
          ( id-iso-Synthetic-Category-Theory ι t))
        ( inv-iso-Synthetic-Category-Theory ν
          ( associative-comp-functor-Synthetic-Category-Theory Α
            ( right-functor-cospan-Synthetic-Category-Theory κ S)
            ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ c)
            ( t))))
      ( associative-comp-functor-Synthetic-Category-Theory Α
        ( left-functor-cospan-Synthetic-Category-Theory κ S)
        ( left-functor-cone-diagram-Synthetic-Category-Theory κ μ c)
        ( t))
      ( horizontal-comp-iso-Synthetic-Category-Theory Χ
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( id-iso-Synthetic-Category-Theory ι
            (left-functor-cospan-Synthetic-Category-Theory κ S))
          ( id-iso-Synthetic-Category-Theory ι
            ( left-functor-cone-diagram-Synthetic-Category-Theory κ μ c)))
        ( α))
      ( pasting-commuting-squares-isomorphisms-Synthetic-Category-Theory
        κ μ ι ν Α Χ
        ( inv-iso-Synthetic-Category-Theory ν
          ( associative-comp-functor-Synthetic-Category-Theory Α
            ( right-functor-cospan-Synthetic-Category-Theory κ S)
            ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ c)
            ( s)))
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( iso-cone-diagram-Synthetic-Category-Theory κ μ c)
          ( id-iso-Synthetic-Category-Theory ι s))
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( horizontal-comp-iso-Synthetic-Category-Theory Χ
            ( id-iso-Synthetic-Category-Theory ι
              ( left-functor-cospan-Synthetic-Category-Theory κ S))
            ( id-iso-Synthetic-Category-Theory ι
              ( left-functor-cone-diagram-Synthetic-Category-Theory κ μ c)))
          ( α))
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( id-iso-Synthetic-Category-Theory ι
            ( right-functor-cospan-Synthetic-Category-Theory κ S))
          ( horizontal-comp-iso-Synthetic-Category-Theory Χ
            ( id-iso-Synthetic-Category-Theory ι
              ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ c))
            ( α)))
        ( inv-iso-Synthetic-Category-Theory ν
          ( associative-comp-functor-Synthetic-Category-Theory Α
            ( right-functor-cospan-Synthetic-Category-Theory κ S)
            ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ c)
            ( t)))
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( iso-cone-diagram-Synthetic-Category-Theory κ μ c)
          ( id-iso-Synthetic-Category-Theory ι t))
        ( horizontal-comp-iso-Synthetic-Category-Theory Χ
          ( horizontal-comp-iso-Synthetic-Category-Theory Χ
            ( id-iso-Synthetic-Category-Theory ι
              ( right-functor-cospan-Synthetic-Category-Theory κ S))
            ( id-iso-Synthetic-Category-Theory ι
              ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ c)))
          ( α))
        ( preserves-associativity-comp-functor-horizontal-comp-iso-inv-Synthetic-Category-Theory
          κ μ ι ν Α Χ Λ Ρ Ξ
          ( right-functor-cospan-Synthetic-Category-Theory κ S)
          ( right-functor-cospan-Synthetic-Category-Theory κ S)
          ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ c)
          ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ c)
          s t
          ( id-iso-Synthetic-Category-Theory ι
            ( right-functor-cospan-Synthetic-Category-Theory κ S))
          ( id-iso-Synthetic-Category-Theory ι
            ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ c))
          ( α))
        ( comp-iso-Synthetic-Category-Theory
          ( composition-isomorphism-Synthetic-Category-Theory μ)
          ( interchange-comp-functor-Synthetic-Category-Theory I
            ( iso-cone-diagram-Synthetic-Category-Theory κ μ c)
            ( horizontal-comp-iso-Synthetic-Category-Theory Χ
              ( id-iso-Synthetic-Category-Theory ι
                ( right-functor-cospan-Synthetic-Category-Theory κ S))
              ( id-iso-Synthetic-Category-Theory ι
                ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ c)))
            ( id-iso-Synthetic-Category-Theory ι t)
            ( α))
          ( comp-iso-Synthetic-Category-Theory
            ( composition-isomorphism-Synthetic-Category-Theory μ)
            ( preserves-isomorphism-horizontal-comp-iso-Synthetic-Category-Theory
              ( M)
              ( inv-iso-Synthetic-Category-Theory
                ( inverse-isomorphism-Synthetic-Category-Theory ν)
                ( left-unit-law-comp-functor-Synthetic-Category-Theory
                  ( left-unit-law-composition-isomorphism-Synthetic-Category-Theory
                    Λ)
                  ( α)))
              ( comp-iso-Synthetic-Category-Theory
                ( composition-isomorphism-Synthetic-Category-Theory μ)
                ( horizontal-comp-iso-Synthetic-Category-Theory
                  ( horizontal-composition-isomorphism-Synthetic-Category-Theory
                    Χ)
                  ( id-iso-Synthetic-Category-Theory
                    ( identity-isomorphism-Synthetic-Category-Theory ι)
                    ( iso-cone-diagram-Synthetic-Category-Theory κ μ c))
                  ( inv-iso-Synthetic-Category-Theory
                    ( inverse-isomorphism-Synthetic-Category-Theory ν)
                    ( preserves-identity-horizontal-comp-iso-Synthetic-Category-Theory
                      N)))
                ( inv-iso-Synthetic-Category-Theory
                  ( inverse-isomorphism-Synthetic-Category-Theory ν)
                  ( right-unit-law-comp-functor-Synthetic-Category-Theory
                    ( right-unit-law-composition-isomorphism-Synthetic-Category-Theory
                      Ρ)
                    ( iso-cone-diagram-Synthetic-Category-Theory κ μ c)))))
            ( comp-iso-Synthetic-Category-Theory
              ( composition-isomorphism-Synthetic-Category-Theory μ)
              ( preserves-isomorphism-horizontal-comp-iso-Synthetic-Category-Theory
                ( M)
                ( right-unit-law-comp-functor-Synthetic-Category-Theory
                  ( right-unit-law-composition-isomorphism-Synthetic-Category-Theory
                    Ρ)
                  ( α))
                ( comp-iso-Synthetic-Category-Theory
                  ( composition-isomorphism-Synthetic-Category-Theory μ)
                  ( left-unit-law-comp-functor-Synthetic-Category-Theory
                    ( left-unit-law-composition-isomorphism-Synthetic-Category-Theory
                      Λ)
                    ( iso-cone-diagram-Synthetic-Category-Theory κ μ c))
                  ( horizontal-comp-iso-Synthetic-Category-Theory
                    ( horizontal-composition-isomorphism-Synthetic-Category-Theory
                      Χ)
                    ( preserves-identity-horizontal-comp-iso-Synthetic-Category-Theory
                      N)
                    ( id-iso-Synthetic-Category-Theory
                      ( identity-isomorphism-Synthetic-Category-Theory ι)
                      ( iso-cone-diagram-Synthetic-Category-Theory κ μ c)))))
                  ( inv-iso-Synthetic-Category-Theory
                    ( inverse-isomorphism-Synthetic-Category-Theory ν)
                    ( interchange-comp-functor-Synthetic-Category-Theory I
                      ( horizontal-comp-iso-Synthetic-Category-Theory Χ
                        ( id-iso-Synthetic-Category-Theory ι
                          ( left-functor-cospan-Synthetic-Category-Theory κ S))
                        ( id-iso-Synthetic-Category-Theory ι
                          ( left-functor-cone-diagram-Synthetic-Category-Theory
                            κ μ c)))
                      ( iso-cone-diagram-Synthetic-Category-Theory κ μ c)
                      ( α)
                      ( id-iso-Synthetic-Category-Theory ι s)))))))
      ( preserves-associativity-comp-functor-horizontal-comp-iso-Synthetic-Category-Theory
        ( Ξ)
        ( id-iso-Synthetic-Category-Theory ι
          ( left-functor-cospan-Synthetic-Category-Theory κ S))
        ( id-iso-Synthetic-Category-Theory ι
          ( left-functor-cone-diagram-Synthetic-Category-Theory κ μ c))
        ( α))
```
