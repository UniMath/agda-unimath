# Descent data for families of equivalence types over the circle

```agda
module synthetic-homotopy-theory.descent-circle-equivalence-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.descent-circle
open import synthetic-homotopy-theory.descent-circle-dependent-pair-types
open import synthetic-homotopy-theory.descent-circle-function-types
open import synthetic-homotopy-theory.descent-circle-subtypes
open import synthetic-homotopy-theory.free-loops
open import synthetic-homotopy-theory.sections-descent-circle
open import synthetic-homotopy-theory.universal-property-circle
```

</details>

## Idea

## Properties

### Characterization of descent data for families of equivalence types over the circle

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-descent-data-circle l l3)
  where

  dependent-descent-data-circle-is-equiv :
    dependent-descent-data-circle
      ( descent-data-circle-function-type l A B)
      ( l2 ⊔ l3)
  pr1 dependent-descent-data-circle-is-equiv = is-equiv
  pr2 dependent-descent-data-circle-is-equiv f =
    equiv-is-equiv-postcomp-is-equiv
      ( aut-family-with-descent-data-circle B) ∘e
    ( equiv-is-equiv-precomp-is-equiv
      ( inv-equiv (aut-family-with-descent-data-circle A)))

  family-with-dependent-descent-data-circle-is-equiv :
    family-with-dependent-descent-data-circle l
      ( family-with-descent-data-circle-function-type l A B)
      ( l2 ⊔ l3)
  pr1 family-with-dependent-descent-data-circle-is-equiv t = is-equiv
  pr1 (pr2 family-with-dependent-descent-data-circle-is-equiv) =
    dependent-descent-data-circle-is-equiv
  pr1 (pr2 (pr2 family-with-dependent-descent-data-circle-is-equiv)) f =
    equiv-is-equiv-postcomp-is-equiv
      ( equiv-family-with-descent-data-circle B) ∘e
    ( equiv-is-equiv-precomp-is-equiv
      ( inv-equiv (equiv-family-with-descent-data-circle A)))
  pr2 (pr2 (pr2 family-with-dependent-descent-data-circle-is-equiv)) f p =
    center (is-property-is-equiv _ _ _)

  family-with-descent-data-circle-equivalence-type :
    family-with-descent-data-circle l (l2 ⊔ l3)
  family-with-descent-data-circle-equivalence-type =
    family-with-descent-data-circle-dependent-pair-type l
      ( family-with-descent-data-circle-function-type l A B)
      ( family-with-dependent-descent-data-circle-is-equiv)
```

### A family of equivalences between families over the circle is given by an equivalence of the corresponding descent data

```agda
  equiv-section-descent-data-circle-equiv-Eq-descent-data-circle :
    dependent-universal-property-circle (l2 ⊔ l3) l →
    ( (t : S) →
      ( family-family-with-descent-data-circle A t) ≃
      ( family-family-with-descent-data-circle B t)) ≃
    ( Eq-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( descent-data-family-with-descent-data-circle B))
  equiv-section-descent-data-circle-equiv-Eq-descent-data-circle dup-circle =
    equivalence-reasoning
    ( (t : S) →
        family-family-with-descent-data-circle A t ≃
        family-family-with-descent-data-circle B t)
    ≃ Σ ( fixpoint-descent-data-circle
          ( descent-data-circle-function-type l A B))
        ( λ x → is-equiv (pr1 x))
      by
        equiv-section-descent-data-circle-subtype-fixpoint-in-subtype l
          ( family-with-descent-data-circle-function-type l A B)
          ( family-with-dependent-descent-data-circle-is-equiv)
          ( λ t f → is-property-is-equiv f)
          ( dup-circle)
    ≃ Σ ( hom-descent-data-circle
          ( descent-data-family-with-descent-data-circle A)
          ( descent-data-family-with-descent-data-circle B))
        ( λ h →
          is-equiv
            ( map-hom-descent-data-circle
              ( descent-data-family-with-descent-data-circle A)
              ( descent-data-family-with-descent-data-circle B)
              ( h)))
      by
        equiv-Σ-equiv-base
          ( λ h →
            is-equiv
              ( map-hom-descent-data-circle
                ( descent-data-family-with-descent-data-circle A)
                ( descent-data-family-with-descent-data-circle B)
                ( h)))
          ( equiv-fixpoint-descent-data-circle-function-type-hom l A B)
    ≃ Eq-descent-data-circle
        ( descent-data-family-with-descent-data-circle A)
        ( descent-data-family-with-descent-data-circle B)
      by
        inv-equiv
          ( equiv-Eq-descent-data-circle-hom-is-equiv
            ( descent-data-family-with-descent-data-circle A)
            ( descent-data-family-with-descent-data-circle B))
```
