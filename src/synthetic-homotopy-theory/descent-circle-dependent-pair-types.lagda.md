# Descent data for dependent pair types over the circle

```agda
module synthetic-homotopy-theory.descent-circle-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport
open import foundation.universe-levels

open import synthetic-homotopy-theory.descent-circle
open import synthetic-homotopy-theory.free-loops
open import synthetic-homotopy-theory.sections-descent-circle
open import synthetic-homotopy-theory.universal-property-circle
```

</details>

## Idea

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-dependent-descent-data-circle l A l3)
  where

  family-descent-data-circle-dependent-pair-type : S → UU (l2 ⊔ l3)
  family-descent-data-circle-dependent-pair-type x =
    Σ ( family-family-with-descent-data-circle A x)
      ( family-family-with-dependent-descent-data-circle A B x)

  descent-data-circle-dependent-pair-type : descent-data-circle (l2 ⊔ l3)
  pr1 descent-data-circle-dependent-pair-type =
    Σ ( type-family-with-descent-data-circle A)
      ( type-family-with-dependent-descent-data-circle A B)
  pr2 descent-data-circle-dependent-pair-type =
    equiv-Σ
      ( type-family-with-dependent-descent-data-circle A B)
      ( aut-family-with-descent-data-circle A)
      ( pseudo-aut-family-with-dependent-descent-data-circle A B)

  eq-descent-data-circle-dependent-pair-type :
    Eq-descent-data-circle
      ( descent-data-circle-dependent-pair-type)
      ( ev-descent-data-circle l family-descent-data-circle-dependent-pair-type)
  pr1 eq-descent-data-circle-dependent-pair-type =
    equiv-Σ
      ( family-family-with-dependent-descent-data-circle A B (base-free-loop l))
      ( equiv-family-with-descent-data-circle A)
      ( equiv-family-with-dependent-descent-data-circle A B)
  pr2 eq-descent-data-circle-dependent-pair-type u =
    inv
      ( tr-Σ
          ( family-family-with-dependent-descent-data-circle A B)
          ( loop-free-loop l)
          ( map-Σ
            ( family-family-with-dependent-descent-data-circle A B
              ( base-free-loop l))
            ( map-equiv-family-with-descent-data-circle A)
            ( map-equiv-family-with-dependent-descent-data-circle A B)
            ( u)) ∙
        eq-pair-Σ
          ( inv (coherence-square-family-with-descent-data-circle A (pr1 u)))
          ( inv
            ( coherence-square-family-with-dependent-descent-data-circle A B
              ( pr1 u)
              ( pr2 u) ∙
              tr-eq-pair-Σ
                ( ind-Σ (family-family-with-dependent-descent-data-circle A B))
                ( loop-free-loop l)
                ( inv
                  ( coherence-square-family-with-descent-data-circle A (pr1 u)))
                ( map-equiv-family-with-dependent-descent-data-circle A B
                  ( pr1 u)
                  ( pr2 u)))))

  family-with-descent-data-circle-dependent-pair-type :
    family-with-descent-data-circle l (l2 ⊔ l3)
  pr1 family-with-descent-data-circle-dependent-pair-type =
    family-descent-data-circle-dependent-pair-type
  pr1 (pr2 family-with-descent-data-circle-dependent-pair-type) =
    descent-data-circle-dependent-pair-type
  pr2 (pr2 family-with-descent-data-circle-dependent-pair-type) =
    eq-descent-data-circle-dependent-pair-type
```
