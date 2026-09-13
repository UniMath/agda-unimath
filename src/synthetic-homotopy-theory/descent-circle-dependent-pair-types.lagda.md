# Descent data for families of dependent pair types over the circle

```agda
module synthetic-homotopy-theory.descent-circle-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.dependent-descent-circle
open import synthetic-homotopy-theory.descent-circle
open import synthetic-homotopy-theory.free-loops
```

</details>

## Idea

Given a family `A : 𝕊¹ → 𝒰` over the
[circle](synthetic-homotopy-theory.circle.md) and a family
`B : (t : 𝕊¹) → (A t) → 𝒰` over `A`, the
[descent data](synthetic-homotopy-theory.descent-circle.md) for the family of
[dependent pair types](foundation.dependent-pair-types.md) `λ t → Σ (A t) (B t)`
is `(Σ X R, map-Σ e k)`, where `(X, e)` is descent data for `A` and `(R, k)` is
dependent descent data for `B`.

## Definitions

### Descent data for families of dependent pair types over the circle

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : double-family-with-dependent-descent-data-circle l A l3)
  where

  descent-data-circle-dependent-pair-type : descent-data-circle (l2 ⊔ l3)
  pr1 descent-data-circle-dependent-pair-type =
    Σ ( type-family-with-descent-data-circle A)
      ( type-double-family-with-dependent-descent-data-circle A B)
  pr2 descent-data-circle-dependent-pair-type =
    equiv-Σ
      ( type-double-family-with-dependent-descent-data-circle A B)
      ( aut-family-with-descent-data-circle A)
      ( dependent-automorphism-double-family-with-dependent-descent-data-circle
        ( A)
        ( B))

  family-descent-data-circle-dependent-pair-type : S → UU (l2 ⊔ l3)
  family-descent-data-circle-dependent-pair-type x =
    Σ ( family-family-with-descent-data-circle A x)
      ( double-family-double-family-with-dependent-descent-data-circle A B x)
```

## Properties

### Characterization of descent data for families of dependent pair types over the circle

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : double-family-with-dependent-descent-data-circle l A l3)
  where

  eq-descent-data-circle-dependent-pair-type :
    equiv-descent-data-circle
      ( descent-data-circle-dependent-pair-type l A B)
      ( descent-data-family-circle l
        ( family-descent-data-circle-dependent-pair-type l A B))
  pr1 eq-descent-data-circle-dependent-pair-type =
    equiv-Σ
      ( double-family-double-family-with-dependent-descent-data-circle A B
        ( base-free-loop l))
      ( equiv-family-with-descent-data-circle A)
      ( equiv-double-family-with-dependent-descent-data-circle A B)
  pr2 eq-descent-data-circle-dependent-pair-type u =
    inv
      ( tr-Σ
          ( double-family-double-family-with-dependent-descent-data-circle A B)
          ( loop-free-loop l)
          ( map-Σ
            ( double-family-double-family-with-dependent-descent-data-circle
              ( A)
              ( B)
              ( base-free-loop l))
            ( map-equiv-family-with-descent-data-circle A)
            ( map-equiv-double-family-with-dependent-descent-data-circle A B)
            ( u)) ∙
        eq-pair-Σ
          ( inv (coherence-square-family-with-descent-data-circle A (pr1 u)))
          ( inv
            ( coherence-square-double-family-with-dependent-descent-data-circle
              ( A)
              ( B)
              ( pr1 u)
              ( pr2 u) ∙
              tr-eq-pair-Σ
                ( ind-Σ
                  ( double-family-double-family-with-dependent-descent-data-circle
                    ( A)
                    ( B)))
                ( loop-free-loop l)
                ( inv
                  ( coherence-square-family-with-descent-data-circle A (pr1 u)))
                ( map-equiv-double-family-with-dependent-descent-data-circle A B
                  ( pr1 u)
                  ( pr2 u)))))

  family-with-descent-data-circle-dependent-pair-type :
    family-with-descent-data-circle l (l2 ⊔ l3)
  pr1 family-with-descent-data-circle-dependent-pair-type =
    family-descent-data-circle-dependent-pair-type l A B
  pr1 (pr2 family-with-descent-data-circle-dependent-pair-type) =
    descent-data-circle-dependent-pair-type l A B
  pr2 (pr2 family-with-descent-data-circle-dependent-pair-type) =
    eq-descent-data-circle-dependent-pair-type
```
