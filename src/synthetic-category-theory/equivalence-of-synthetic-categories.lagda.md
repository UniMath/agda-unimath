# Equivalence of synthetic categories

```agda
{-# OPTIONS --guardedness #-}

module synthetic-category-theory.equivalence-of-synthetic-categories where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.globular-types

open import synthetic-category-theory.synthetic-categories
```

</details>

## Definitions

### Sections, retractions and equivalences

Consider a functor f : C → D. A section of f is a functor s : D → C together
with an isomorphism fs ≅ id_C. A retraction of f is a functor r : D → C together
with an isomorphism rf ≅ id_D. The functor f is an equivalence if there is a
functor g : D → C together with isomorphisms fg ≅ id_C and gf ≅ id_D.

```agda
module _
  {l : Level}
  where

  is-section-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l) →
    (μ : composition-Synthetic-Category-Theory κ) →
    (ι : identity-Synthetic-Category-Theory κ) →
    (C D : category-Synthetic-Category-Theory κ) →
    (f : functor-Synthetic-Category-Theory κ C D) →
    (s : functor-Synthetic-Category-Theory κ D C) → UU l
  is-section-Synthetic-Category-Theory κ μ ι C D f s =
    isomorphism-Synthetic-Category-Theory
      ( κ)
      ( comp-functor-Synthetic-Category-Theory μ f s)
      ( id-functor-Synthetic-Category-Theory ι D)

  section-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l) →
    (μ : composition-Synthetic-Category-Theory κ) →
    (ι : identity-Synthetic-Category-Theory κ) →
    (C D : category-Synthetic-Category-Theory κ) →
    (f : functor-Synthetic-Category-Theory κ C D) → UU l
  section-Synthetic-Category-Theory κ μ ι C D f =
    Σ ( functor-Synthetic-Category-Theory κ D C)
      ( λ s → is-section-Synthetic-Category-Theory κ μ ι C D f s)

  map-section-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l) →
    (μ : composition-Synthetic-Category-Theory κ) →
    (ι : identity-Synthetic-Category-Theory κ) →
    (C D : category-Synthetic-Category-Theory κ) →
    (f : functor-Synthetic-Category-Theory κ C D) →
    section-Synthetic-Category-Theory κ μ ι C D f →
    functor-Synthetic-Category-Theory κ D C
  map-section-Synthetic-Category-Theory κ μ ι C D f sec = pr1 sec

  is-section-section-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l) →
    (μ : composition-Synthetic-Category-Theory κ) →
    (ι : identity-Synthetic-Category-Theory κ) →
    (C D : category-Synthetic-Category-Theory κ) →
    (f : functor-Synthetic-Category-Theory κ C D) →
    (sec : section-Synthetic-Category-Theory κ μ ι C D f) →
    is-section-Synthetic-Category-Theory
      κ μ ι C D f (map-section-Synthetic-Category-Theory κ μ ι C D f sec)
  is-section-section-Synthetic-Category-Theory κ μ ι C D f sec = pr2 sec

  is-retraction-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l) →
    (μ : composition-Synthetic-Category-Theory κ) →
    (ι : identity-Synthetic-Category-Theory κ) →
    (C D : category-Synthetic-Category-Theory κ) →
    (f : functor-Synthetic-Category-Theory κ C D) →
    (r : functor-Synthetic-Category-Theory κ D C) → UU l
  is-retraction-Synthetic-Category-Theory κ μ ι C D f r =
    isomorphism-Synthetic-Category-Theory
      ( κ)
      ( comp-functor-Synthetic-Category-Theory μ r f)
      ( id-functor-Synthetic-Category-Theory ι C)

  retraction-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l) →
    (μ : composition-Synthetic-Category-Theory κ) →
    (ι : identity-Synthetic-Category-Theory κ) →
    (C D : category-Synthetic-Category-Theory κ) →
    (f : functor-Synthetic-Category-Theory κ C D) → UU l
  retraction-Synthetic-Category-Theory κ μ ι C D f =
    Σ ( functor-Synthetic-Category-Theory κ D C)
      ( λ r → is-retraction-Synthetic-Category-Theory κ μ ι C D f r)

  map-retraction-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l) →
    (μ : composition-Synthetic-Category-Theory κ) →
    (ι : identity-Synthetic-Category-Theory κ) →
    (C D : category-Synthetic-Category-Theory κ) →
    (f : functor-Synthetic-Category-Theory κ C D) →
    (retraction-Synthetic-Category-Theory κ μ ι C D f) →
    (functor-Synthetic-Category-Theory κ D C)
  map-retraction-Synthetic-Category-Theory κ μ ι C D f ret = pr1 ret

  is-retraction-retraction-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l) →
    (μ : composition-Synthetic-Category-Theory κ) →
    (ι : identity-Synthetic-Category-Theory κ) →
    (C D : category-Synthetic-Category-Theory κ) →
    (f : functor-Synthetic-Category-Theory κ C D) →
    (ret : retraction-Synthetic-Category-Theory κ μ ι C D f) →
    is-retraction-Synthetic-Category-Theory
      κ μ ι C D f (map-retraction-Synthetic-Category-Theory κ μ ι C D f ret)
  is-retraction-retraction-Synthetic-Category-Theory κ μ ι C D f ret = pr2 ret

  is-equivalence-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l) →
    (μ : composition-Synthetic-Category-Theory κ) →
    (ι : identity-Synthetic-Category-Theory κ) →
    (C D : category-Synthetic-Category-Theory κ) →
    (f : functor-Synthetic-Category-Theory κ C D)
    (g : functor-Synthetic-Category-Theory κ D C) → UU l
  is-equivalence-Synthetic-Category-Theory κ μ ι C D f g =
        ( is-section-Synthetic-Category-Theory κ μ ι C D f g)
          ×
        ( is-retraction-Synthetic-Category-Theory κ μ ι C D f g)

  equivalence-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l) →
    (μ : composition-Synthetic-Category-Theory κ) →
    (ι : identity-Synthetic-Category-Theory κ) →
    (C D : category-Synthetic-Category-Theory κ) →
    (f : functor-Synthetic-Category-Theory κ C D) → UU l
  equivalence-Synthetic-Category-Theory κ μ ι C D f =
    Σ ( functor-Synthetic-Category-Theory κ D C)
      ( λ g → is-equivalence-Synthetic-Category-Theory κ μ ι C D f g)

  map-equivalence-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l) →
    (μ : composition-Synthetic-Category-Theory κ) →
    (ι : identity-Synthetic-Category-Theory κ) →
    (C D : category-Synthetic-Category-Theory κ) →
    (f : functor-Synthetic-Category-Theory κ C D) →
    equivalence-Synthetic-Category-Theory κ μ ι C D f →
    functor-Synthetic-Category-Theory κ D C
  map-equivalence-Synthetic-Category-Theory κ μ ι C D f eq = pr1 eq

  is-equivalence-equivalence-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l) →
    (μ : composition-Synthetic-Category-Theory κ) →
    (ι : identity-Synthetic-Category-Theory κ) →
    (C D : category-Synthetic-Category-Theory κ) →
    (f : functor-Synthetic-Category-Theory κ C D) →
    (eq : equivalence-Synthetic-Category-Theory κ μ ι C D f) →
    is-equivalence-Synthetic-Category-Theory
      κ μ ι C D f (map-equivalence-Synthetic-Category-Theory κ μ ι C D f eq)
  is-equivalence-equivalence-Synthetic-Category-Theory κ μ ι C D f eq = pr2 eq

  is-section-equivalence-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l) →
    (μ : composition-Synthetic-Category-Theory κ) →
    (ι : identity-Synthetic-Category-Theory κ) →
    (C D : category-Synthetic-Category-Theory κ) →
    (f : functor-Synthetic-Category-Theory κ C D) →
    (eq : equivalence-Synthetic-Category-Theory κ μ ι C D f) →
    is-section-Synthetic-Category-Theory
      κ μ ι C D f (map-equivalence-Synthetic-Category-Theory κ μ ι C D f eq)
  is-section-equivalence-Synthetic-Category-Theory κ μ ι C D f eq =
    pr1 (is-equivalence-equivalence-Synthetic-Category-Theory κ μ ι C D f eq)

  is-retraction-equivalence-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l) →
    (μ : composition-Synthetic-Category-Theory κ) →
    (ι : identity-Synthetic-Category-Theory κ) →
    (C D : category-Synthetic-Category-Theory κ) →
    (f : functor-Synthetic-Category-Theory κ C D) →
    (eq : equivalence-Synthetic-Category-Theory κ μ ι C D f) →
    is-retraction-Synthetic-Category-Theory
      κ μ ι C D f (map-equivalence-Synthetic-Category-Theory κ μ ι C D f eq)
  is-retraction-equivalence-Synthetic-Category-Theory κ μ ι C D f eq =
    pr2 (is-equivalence-equivalence-Synthetic-Category-Theory κ μ ι C D f eq)
```

A functor f : C → D admits a section and a retraction iff it is an equivalence
(Lemma 1.1.6. in the book.)

```agda
  is-equivalence-admits-section-admits-retraction-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l) →
    (μ : composition-Synthetic-Category-Theory κ) →
    (ι : identity-Synthetic-Category-Theory κ) →
    (C D : category-Synthetic-Category-Theory κ) →
    (f : functor-Synthetic-Category-Theory κ C D) →
    equivalence-Synthetic-Category-Theory κ μ ι C D f →
    (section-Synthetic-Category-Theory κ μ ι C D f)
      ×
    (retraction-Synthetic-Category-Theory κ μ ι C D f)
  is-equivalence-admits-section-admits-retraction-Synthetic-Category-Theory
    κ μ ι C D f eq =
      ( map-equivalence-Synthetic-Category-Theory κ μ ι C D f eq ,
        pr1
        (is-equivalence-equivalence-Synthetic-Category-Theory κ μ ι C D f eq)) ,
      ( map-equivalence-Synthetic-Category-Theory κ μ ι C D f eq ,
        pr2
        (is-equivalence-equivalence-Synthetic-Category-Theory κ μ ι C D f eq))

  admits-section-admits-retraction-is-equivalence-Synthetic-Category-Theory :
    (κ : language-Synthetic-Category-Theory l) →
    (μ : composition-Synthetic-Category-Theory κ) →
    (ι : identity-Synthetic-Category-Theory κ) →
    (ν : inverse-Synthetic-Category-Theory κ) →
    (Λ : left-unit-law-composition-Synthetic-Category-Theory κ ι μ) →
    (Ρ : right-unit-law-composition-Synthetic-Category-Theory κ ι μ) →
    (X : horizontal-composition-Synthetic-Category-Theory κ μ) →
    (Α : associative-composition-Synthetic-Category-Theory κ μ) →
    (C D : category-Synthetic-Category-Theory κ) →
    (f : functor-Synthetic-Category-Theory κ C D) →
    section-Synthetic-Category-Theory κ μ ι C D f →
    retraction-Synthetic-Category-Theory κ μ ι C D f →
    equivalence-Synthetic-Category-Theory κ μ ι C D f
  admits-section-admits-retraction-is-equivalence-Synthetic-Category-Theory
    κ μ ι ν Λ Ρ Χ Α C D f sec ret =
    let
      s = map-section-Synthetic-Category-Theory κ μ ι C D f sec
      Ξ = is-section-section-Synthetic-Category-Theory κ μ ι C D f sec
      r = map-retraction-Synthetic-Category-Theory κ μ ι C D f ret
      Ψ = is-retraction-retraction-Synthetic-Category-Theory κ μ ι C D f ret
      α = comp-iso-Synthetic-Category-Theory μ
          ( comp-iso-Synthetic-Category-Theory μ
            ( comp-iso-Synthetic-Category-Theory μ
              ( comp-iso-Synthetic-Category-Theory μ
                ( right-unit-law-comp-functor-Synthetic-Category-Theory Ρ r)
                ( horizontal-comp-iso-Synthetic-Category-Theory Χ
                  (id-iso-Synthetic-Category-Theory ι r) Ξ))
              ( associative-comp-functor-Synthetic-Category-Theory Α r f s))
            ( horizontal-comp-iso-Synthetic-Category-Theory Χ
              ( inv-iso-Synthetic-Category-Theory ν Ψ)
              ( id-iso-Synthetic-Category-Theory ι s)))
            ( inv-iso-Synthetic-Category-Theory ν
              ( left-unit-law-comp-functor-Synthetic-Category-Theory Λ s))
      β = comp-iso-Synthetic-Category-Theory μ
            ( Ψ)
            ( horizontal-comp-iso-Synthetic-Category-Theory Χ
              ( α)
              ( id-iso-Synthetic-Category-Theory ι f))
    in
    s , Ξ , β
```

Equivalences are closed under composition (lemma 1.1.8.)

```agda
module _
  {l : Level} {κ : language-Synthetic-Category-Theory l}
  {μ : composition-Synthetic-Category-Theory κ}
  {ι : identity-Synthetic-Category-Theory κ}
  {ν : inverse-Synthetic-Category-Theory κ}
  {Λ : left-unit-law-composition-Synthetic-Category-Theory κ ι μ}
  {Ρ : right-unit-law-composition-Synthetic-Category-Theory κ ι μ}
  {Χ : horizontal-composition-Synthetic-Category-Theory κ μ}
  {Α : associative-composition-Synthetic-Category-Theory κ μ}
  where

  equiv-equiv-comp-equiv-Synthetic-Category-Theory :
    (C D E : category-Synthetic-Category-Theory κ) →
    (f' : functor-Synthetic-Category-Theory κ D E) →
    (f : functor-Synthetic-Category-Theory κ C D) →
    (eq-f' : equivalence-Synthetic-Category-Theory κ μ ι D E f') →
    (eq-f : equivalence-Synthetic-Category-Theory κ μ ι C D f) →
    equivalence-Synthetic-Category-Theory
      κ μ ι C E (comp-functor-Synthetic-Category-Theory μ f' f)
  equiv-equiv-comp-equiv-Synthetic-Category-Theory
    C D E f' f eq-f' eq-f =
      let
        g = map-equivalence-Synthetic-Category-Theory κ μ ι C D f eq-f
        g' = map-equivalence-Synthetic-Category-Theory κ μ ι D E f' eq-f'
      in
      comp-functor-Synthetic-Category-Theory μ g g' ,
      comp-iso-Synthetic-Category-Theory μ
        ( is-section-equivalence-Synthetic-Category-Theory κ μ ι D E f' eq-f')
        ( comp-iso-Synthetic-Category-Theory μ
          ( horizontal-comp-iso-Synthetic-Category-Theory Χ
            ( right-unit-law-comp-functor-Synthetic-Category-Theory Ρ f')
            ( id-iso-Synthetic-Category-Theory ι g'))
          ( comp-iso-Synthetic-Category-Theory μ
            ( horizontal-comp-iso-Synthetic-Category-Theory Χ
              ( horizontal-comp-iso-Synthetic-Category-Theory Χ
                ( id-iso-Synthetic-Category-Theory ι f')
                ( is-section-equivalence-Synthetic-Category-Theory
                  κ μ ι C D f eq-f))
              ( id-iso-Synthetic-Category-Theory ι g'))
            ( comp-iso-Synthetic-Category-Theory μ
              ( horizontal-comp-iso-Synthetic-Category-Theory Χ
                ( associative-comp-functor-Synthetic-Category-Theory Α f' f g)
                ( id-iso-Synthetic-Category-Theory ι g'))
              ( inv-iso-Synthetic-Category-Theory ν
                ( associative-comp-functor-Synthetic-Category-Theory Α
                  ( comp-functor-Synthetic-Category-Theory μ f' f)
                  ( g)
                  ( g')))))) ,
      comp-iso-Synthetic-Category-Theory μ
        ( is-retraction-equivalence-Synthetic-Category-Theory κ μ ι C D f eq-f)
        ( comp-iso-Synthetic-Category-Theory μ
          ( horizontal-comp-iso-Synthetic-Category-Theory Χ
            ( right-unit-law-comp-functor-Synthetic-Category-Theory Ρ g)
            ( id-iso-Synthetic-Category-Theory ι f))
          ( comp-iso-Synthetic-Category-Theory μ
            ( horizontal-comp-iso-Synthetic-Category-Theory Χ
              ( horizontal-comp-iso-Synthetic-Category-Theory Χ
                ( id-iso-Synthetic-Category-Theory ι g)
                ( is-retraction-equivalence-Synthetic-Category-Theory
                  κ μ ι D E f' eq-f'))
              ( id-iso-Synthetic-Category-Theory ι f))
            ( comp-iso-Synthetic-Category-Theory μ
              ( horizontal-comp-iso-Synthetic-Category-Theory Χ
                ( associative-comp-functor-Synthetic-Category-Theory Α g g' f')
                ( id-iso-Synthetic-Category-Theory ι f))
              ( inv-iso-Synthetic-Category-Theory ν
                ( associative-comp-functor-Synthetic-Category-Theory Α
                  ( comp-functor-Synthetic-Category-Theory μ g g')
                  ( f')
                  ( f))))))
```
