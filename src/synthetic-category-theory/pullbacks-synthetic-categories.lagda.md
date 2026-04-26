# Pullbacks of synthetic categories

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.pullbacks-synthetic-categories where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import globular-types.globular-types

open import synthetic-category-theory.cone-diagrams-synthetic-categories
open import synthetic-category-theory.cospans-synthetic-categories
open import synthetic-category-theory.equivalences-synthetic-categories
open import synthetic-category-theory.synthetic-categories
```

</details>

## Idea

Consider a
[cospan diagram](synthetic-category-theory.cospans-synthetic-categories.md) S of
[synthetic categories](synthetic-category-theory.synthetic-categories.md). The
{{#concept "pullback" Disambiguation="Synthetic categories"}} of S is a cone
diagram cᵤ = (pr₀, pr₁, τᵤ) over S with apex P that is universal in the sense
that:

```text
1) for every cone diagram c = (t₀, t₁, τ) over S with apex T there exists a functor
  (t₀, t₁) : T → P together with an isomorphism of cone diagrams c ≅ (t₀, t₁)*(cᵤ)
2) given two functors f,g : T → P equipped with an isomorphism of cone diagrams
  s*(cᵤ) ≅ t*(cᵤ), there exists a natural isomorphism s ≅ t that induces the said
  isomorphism of cone diagrams.
```

```agda
module _
  {l : Level}
  where

  record
    pullback-Synthetic-Category-Theory
      (κ : language-Synthetic-Category-Theory l)
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
      (M :
        preserves-isomorphism-horizontal-composition-Synthetic-Category-Theory
          κ ι μ Χ)
      (N :
        preserves-identity-horizontal-composition-Synthetic-Category-Theory
          κ ι μ Χ) : UU l
    where
    coinductive
    field
      apex-pullback-Synthetic-Category-Theory :
        {C D E : category-Synthetic-Category-Theory κ} →
        cospan-Synthetic-Category-Theory κ C D E →
          category-Synthetic-Category-Theory κ
      cone-diagram-pullback-Synthetic-Category-Theory :
        {C D E : category-Synthetic-Category-Theory κ}
        (S : cospan-Synthetic-Category-Theory κ C D E) →
          cone-diagram-Synthetic-Category-Theory
            κ μ S ( apex-pullback-Synthetic-Category-Theory S)
      universality-functor-pullback-Synthetic-Category-Theory :
        {C D E : category-Synthetic-Category-Theory κ}
        (S : cospan-Synthetic-Category-Theory κ C D E)
        {T : category-Synthetic-Category-Theory κ}
        (c : cone-diagram-Synthetic-Category-Theory κ μ S T) →
          functor-Synthetic-Category-Theory κ
            T ( apex-pullback-Synthetic-Category-Theory S)
      universality-iso-pullback-Synthetic-Category-Theory :
        {C D E : category-Synthetic-Category-Theory κ}
        (S : cospan-Synthetic-Category-Theory κ C D E)
        (T : category-Synthetic-Category-Theory κ)
        (c : cone-diagram-Synthetic-Category-Theory κ μ S T) →
          iso-of-cone-diagrams-Synthetic-Category-Theory κ μ ι Χ
          ( c)
            ( induced-cone-diagram-Synthetic-Category-Theory κ μ ι ν Χ Α S
              ( cone-diagram-pullback-Synthetic-Category-Theory S)
              ( universality-functor-pullback-Synthetic-Category-Theory S c))
      triviality-iso-of-cone-diagrams-pullback-Synthetic-Category-Theory :
        {C D E : category-Synthetic-Category-Theory κ}
        (S : cospan-Synthetic-Category-Theory κ C D E)
        {T : category-Synthetic-Category-Theory κ}
        (s t :
          functor-Synthetic-Category-Theory κ T
            ( apex-pullback-Synthetic-Category-Theory S))
        (H : iso-of-cone-diagrams-Synthetic-Category-Theory κ μ ι Χ
          (induced-cone-diagram-Synthetic-Category-Theory κ μ ι ν Χ Α S
            ( cone-diagram-pullback-Synthetic-Category-Theory S)
            ( s))
          (induced-cone-diagram-Synthetic-Category-Theory κ μ ι ν Χ Α S
            ( cone-diagram-pullback-Synthetic-Category-Theory S)
            ( t))) →
          Σ ( isomorphism-Synthetic-Category-Theory κ s t)
            λ α →
              iso-of-isos-of-cone-diagrams-Synthetic-Category-Theory κ μ ι ν Χ M
                ( induced-iso-cone-diagram-Synthetic-Category-Theory
                  κ μ ι ν Α Χ Λ Ρ Ξ I M N S
                  ( cone-diagram-pullback-Synthetic-Category-Theory S)
                  s t α)
                ( H)

open pullback-Synthetic-Category-Theory public
```

### The left and right projection functors with domain the apex of the pullback cone

```agda
module _
  {l : Level}
  where

  left-functor-pullback-Synthetic-Category-Theory :
      (κ : language-Synthetic-Category-Theory l)
      (μ : composition-Synthetic-Category-Theory κ)
      {ι : identity-Synthetic-Category-Theory κ}
      {ν : inverse-Synthetic-Category-Theory κ μ ι}
      {Α : associative-composition-Synthetic-Category-Theory κ μ}
      {Χ : horizontal-composition-Synthetic-Category-Theory κ μ}
      {Λ : left-unit-law-composition-Synthetic-Category-Theory κ ι μ}
      {Ρ : right-unit-law-composition-Synthetic-Category-Theory κ ι μ}
      {Ξ :
        preserves-associativity-composition-horizontal-composition-Synthetic-Category-Theory
          κ μ Α Χ}
      {I : interchange-composition-Synthetic-Category-Theory κ μ Χ}
      {Μ :
        preserves-isomorphism-horizontal-composition-Synthetic-Category-Theory
          κ ι μ Χ}
      {Ν :
        preserves-identity-horizontal-composition-Synthetic-Category-Theory
          κ ι μ Χ}
      (PB : pullback-Synthetic-Category-Theory κ μ ι ν Α Χ Λ Ρ Ξ I Μ Ν)
      {C E D : category-Synthetic-Category-Theory κ}
      (S : cospan-Synthetic-Category-Theory κ C E D) →
      functor-Synthetic-Category-Theory κ
        ( apex-pullback-Synthetic-Category-Theory PB S)
        ( left-source-cospan-Synthetic-Category-Theory κ S)
  left-functor-pullback-Synthetic-Category-Theory κ μ PB S =
    left-functor-cone-diagram-Synthetic-Category-Theory κ μ
      ( cone-diagram-pullback-Synthetic-Category-Theory PB S)

  right-functor-pullback-Synthetic-Category-Theory :
      (κ : language-Synthetic-Category-Theory l)
      (μ : composition-Synthetic-Category-Theory κ)
      {ι : identity-Synthetic-Category-Theory κ}
      {ν : inverse-Synthetic-Category-Theory κ μ ι}
      {Α : associative-composition-Synthetic-Category-Theory κ μ}
      {Χ : horizontal-composition-Synthetic-Category-Theory κ μ}
      {Λ : left-unit-law-composition-Synthetic-Category-Theory κ ι μ}
      {Ρ : right-unit-law-composition-Synthetic-Category-Theory κ ι μ}
      {Ξ :
        preserves-associativity-composition-horizontal-composition-Synthetic-Category-Theory
          κ μ Α Χ}
      {I : interchange-composition-Synthetic-Category-Theory κ μ Χ}
      {Μ :
        preserves-isomorphism-horizontal-composition-Synthetic-Category-Theory
          κ ι μ Χ}
      {Ν :
        preserves-identity-horizontal-composition-Synthetic-Category-Theory
          κ ι μ Χ}
      (PB : pullback-Synthetic-Category-Theory κ μ ι ν Α Χ Λ Ρ Ξ I Μ Ν)
      {C E D : category-Synthetic-Category-Theory κ}
      (S : cospan-Synthetic-Category-Theory κ C E D) →
      functor-Synthetic-Category-Theory κ
        ( apex-pullback-Synthetic-Category-Theory PB S)
        ( right-source-cospan-Synthetic-Category-Theory κ S)
  right-functor-pullback-Synthetic-Category-Theory κ μ PB S =
    right-functor-cone-diagram-Synthetic-Category-Theory κ μ
      ( cone-diagram-pullback-Synthetic-Category-Theory PB S)
```

### Functoriality of pullbacks

Taking pullbacks is functorial in the sense that given cospans S and S' and a
transformations of cospans S → S', there exists a preferred functor between the
pullback of S and the pullback of S'.

```agda
module _
  {l : Level}
  where

  functor-pullback-Synthetic-Category-Theory :
      (κ : language-Synthetic-Category-Theory l)
      (μ : composition-Synthetic-Category-Theory κ)
      (ι : identity-Synthetic-Category-Theory κ)
      (ν : inverse-Synthetic-Category-Theory κ μ ι)
      (Α : associative-composition-Synthetic-Category-Theory κ μ)
      (Χ : horizontal-composition-Synthetic-Category-Theory κ μ)
      {Λ : left-unit-law-composition-Synthetic-Category-Theory κ ι μ}
      {Ρ : right-unit-law-composition-Synthetic-Category-Theory κ ι μ}
      {Ξ :
        preserves-associativity-composition-horizontal-composition-Synthetic-Category-Theory
          κ μ Α Χ}
      {I : interchange-composition-Synthetic-Category-Theory κ μ Χ}
      {M :
        preserves-isomorphism-horizontal-composition-Synthetic-Category-Theory
          κ ι μ Χ}
      {N :
        preserves-identity-horizontal-composition-Synthetic-Category-Theory
          κ ι μ Χ}
      (PB : pullback-Synthetic-Category-Theory κ μ ι ν Α Χ Λ Ρ Ξ I M N)
      {C C' E E' D D' : category-Synthetic-Category-Theory κ}
      {S : cospan-Synthetic-Category-Theory κ C E D}
      {S' : cospan-Synthetic-Category-Theory κ C' E' D'} →
      transformation-cospan-Synthetic-Category-Theory κ μ S S' →
      functor-Synthetic-Category-Theory κ
        ( apex-pullback-Synthetic-Category-Theory PB S)
        ( apex-pullback-Synthetic-Category-Theory PB S')
  functor-pullback-Synthetic-Category-Theory
    κ μ ι ν Α Χ PB {S = S} {S' = S'} H =
    universality-functor-pullback-Synthetic-Category-Theory PB S'
      ( comp-functor-Synthetic-Category-Theory μ
        ( right-functor-transformation-cospan-Synthetic-Category-Theory κ μ H)
        ( right-functor-pullback-Synthetic-Category-Theory κ μ PB S) ,
      ( comp-functor-Synthetic-Category-Theory μ
        ( left-functor-transformation-cospan-Synthetic-Category-Theory κ μ H)
        ( left-functor-pullback-Synthetic-Category-Theory κ μ PB S)) ,
      ( comp-iso-Synthetic-Category-Theory μ
        ( associative-comp-functor-Synthetic-Category-Theory Α
          ( left-functor-cospan-Synthetic-Category-Theory κ S')
          ( left-functor-transformation-cospan-Synthetic-Category-Theory κ μ H)
          ( left-functor-pullback-Synthetic-Category-Theory κ μ PB S))
        ( comp-iso-Synthetic-Category-Theory μ
          ( horizontal-comp-iso-Synthetic-Category-Theory Χ
            ( left-commuting-square-transformation-cospan-Synthetic-Category-Theory
              κ μ H)
            ( id-iso-Synthetic-Category-Theory ι
              ( left-functor-pullback-Synthetic-Category-Theory κ μ PB S)))
          ( comp-iso-Synthetic-Category-Theory μ
            ( inv-iso-Synthetic-Category-Theory ν
              ( associative-comp-functor-Synthetic-Category-Theory Α
                ( middle-functor-transformation-cospan-Synthetic-Category-Theory
                  κ μ H)
                ( left-functor-cospan-Synthetic-Category-Theory κ S)
                ( left-functor-cone-diagram-Synthetic-Category-Theory κ μ
                  ( cone-diagram-pullback-Synthetic-Category-Theory PB S))))
            ( comp-iso-Synthetic-Category-Theory μ
              ( horizontal-comp-iso-Synthetic-Category-Theory Χ
                ( id-iso-Synthetic-Category-Theory ι
                  ( middle-functor-transformation-cospan-Synthetic-Category-Theory
                    κ μ H))
                ( iso-cone-diagram-Synthetic-Category-Theory κ μ
                  ( cone-diagram-pullback-Synthetic-Category-Theory PB S)))
              ( comp-iso-Synthetic-Category-Theory μ
                ( associative-comp-functor-Synthetic-Category-Theory Α
                  ( middle-functor-transformation-cospan-Synthetic-Category-Theory
                    κ μ H)
                  ( right-functor-cospan-Synthetic-Category-Theory κ S)
                  ( right-functor-pullback-Synthetic-Category-Theory κ μ PB S))
                ( comp-iso-Synthetic-Category-Theory μ
                  ( horizontal-comp-iso-Synthetic-Category-Theory Χ
                    ( inv-iso-Synthetic-Category-Theory ν
                      ( right-commuting-square-transformation-cospan-Synthetic-Category-Theory
                        κ μ H))
                    ( id-iso-Synthetic-Category-Theory ι
                      ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ
                        ( cone-diagram-pullback-Synthetic-Category-Theory PB
                          S))))
                  ( inv-iso-Synthetic-Category-Theory ν
                    ( associative-comp-functor-Synthetic-Category-Theory Α
                      ( right-functor-cospan-Synthetic-Category-Theory κ S')
                      ( right-functor-transformation-cospan-Synthetic-Category-Theory
                        κ μ H)
                      ( right-functor-cone-diagram-Synthetic-Category-Theory κ μ
                        ( cone-diagram-pullback-Synthetic-Category-Theory
                          PB S)))))))))))
```
