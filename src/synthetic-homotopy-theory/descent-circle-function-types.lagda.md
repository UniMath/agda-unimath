# Descent data for families of function types over the circle

```agda
module synthetic-homotopy-theory.descent-circle-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-function-types
open import foundation.homotopies
open import foundation.homotopy-algebra
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.transport-along-identifications
open import foundation.universal-property-equivalences
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.descent-circle
open import synthetic-homotopy-theory.free-loops
open import synthetic-homotopy-theory.morphisms-descent-data-circle
open import synthetic-homotopy-theory.sections-descent-circle
open import synthetic-homotopy-theory.universal-property-circle
```

</details>

## Idea

Given two families `A, B : 𝕊¹ → 𝒰` over the
[circle](synthetic-homotopy-theory.circle.md), the
[descent data](synthetic-homotopy-theory.descent-circle.md) for the family of
function types `λ t → (A t → B t)` is `(X → Y, λ h → f ∘ h ∘ e⁻¹)`, where
`(X, e)` is descent data for `A` and `(Y, f)` is descent data for `B`.

This correspondence allows us to characterize sections of this family as
homomorphisms from `(X, e)` to `(Y, f)`.

## Definitions

### Descent data for families of function types over the circle

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-descent-data-circle l l3)
  where

  family-descent-data-circle-function-type : S → UU (l2 ⊔ l3)
  family-descent-data-circle-function-type x =
    family-family-with-descent-data-circle A x →
    family-family-with-descent-data-circle B x

  descent-data-circle-function-type : descent-data-circle (l2 ⊔ l3)
  pr1 descent-data-circle-function-type =
    type-family-with-descent-data-circle A →
    type-family-with-descent-data-circle B
  pr2 descent-data-circle-function-type =
    ( equiv-postcomp
      ( type-family-with-descent-data-circle A)
      ( aut-family-with-descent-data-circle B)) ∘e
    ( equiv-precomp
      ( inv-equiv (aut-family-with-descent-data-circle A))
      ( type-family-with-descent-data-circle B))
```

## Properties

### Characterization of descent data for families of function types over the circle

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-descent-data-circle l l3)
  where

  eq-descent-data-circle-function-type :
    equiv-descent-data-circle
      ( descent-data-circle-function-type l A B)
      ( descent-data-family-circle
        ( l)
        ( family-descent-data-circle-function-type l A B))
  pr1 eq-descent-data-circle-function-type =
    ( equiv-postcomp
      ( family-family-with-descent-data-circle A (base-free-loop l))
      ( equiv-family-with-descent-data-circle B)) ∘e
    ( equiv-precomp
      ( inv-equiv (equiv-family-with-descent-data-circle A))
      ( type-family-with-descent-data-circle B))
  pr2 eq-descent-data-circle-function-type h =
    ( eq-htpy
      ( horizontal-concat-htpy
        ( coherence-square-family-with-descent-data-circle B)
        ( h ·l
          inv-htpy
            ( coherence-square-maps-inv-equiv
              ( equiv-family-with-descent-data-circle A)
              ( aut-family-with-descent-data-circle A)
              ( equiv-tr
                ( family-family-with-descent-data-circle A)
                ( loop-free-loop l))
              ( equiv-family-with-descent-data-circle A)
              ( coherence-square-family-with-descent-data-circle A))))) ∙
    ( inv
      ( ( tr-function-type
          ( family-family-with-descent-data-circle A)
          ( family-family-with-descent-data-circle B) (loop-free-loop l))
        ( map-equiv-descent-data-circle
          ( descent-data-circle-function-type l A B)
          ( descent-data-family-circle
            ( l)
            ( family-descent-data-circle-function-type l A B))
          ( eq-descent-data-circle-function-type)
          ( h))))

  family-with-descent-data-circle-function-type :
    family-with-descent-data-circle l (l2 ⊔ l3)
  pr1 family-with-descent-data-circle-function-type =
    family-descent-data-circle-function-type l A B
  pr1 (pr2 family-with-descent-data-circle-function-type) =
    descent-data-circle-function-type l A B
  pr2 (pr2 family-with-descent-data-circle-function-type) =
    eq-descent-data-circle-function-type
```

### Maps between families over the circle are equivalent to homomorphisms between the families' descent data

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-descent-data-circle l l3)
  where

  equiv-fixpoint-descent-data-circle-function-type-hom :
    fixpoint-descent-data-circle (descent-data-circle-function-type l A B) ≃
    hom-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( descent-data-family-with-descent-data-circle B)
  equiv-fixpoint-descent-data-circle-function-type-hom =
    equiv-tot
      ( λ h →
        ( equiv-inv-htpy
          ( map-aut-family-with-descent-data-circle B ∘ h)
          ( h ∘ map-aut-family-with-descent-data-circle A)) ∘e
        ( inv-equiv
          ( equiv-coherence-triangle-maps-inv-top
            ( map-aut-family-with-descent-data-circle B ∘ h)
            ( h)
            ( aut-family-with-descent-data-circle A))) ∘e
        ( equiv-inv-htpy _ _) ∘e
        ( equiv-funext))

  equiv-descent-data-family-circle-function-type-hom :
    dependent-universal-property-circle l →
    ( (x : S) → family-descent-data-circle-function-type l A B x) ≃
    hom-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( descent-data-family-with-descent-data-circle B)
  equiv-descent-data-family-circle-function-type-hom dup-circle =
    equiv-fixpoint-descent-data-circle-function-type-hom ∘e
    ( equiv-ev-fixpoint-descent-data-circle
      ( l)
      ( family-with-descent-data-circle-function-type l A B)
      ( dup-circle))
```
