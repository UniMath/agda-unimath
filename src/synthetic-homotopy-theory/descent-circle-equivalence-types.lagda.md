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

open import synthetic-homotopy-theory.dependent-descent-circle
open import synthetic-homotopy-theory.descent-circle
open import synthetic-homotopy-theory.descent-circle-dependent-pair-types
open import synthetic-homotopy-theory.descent-circle-function-types
open import synthetic-homotopy-theory.descent-circle-subtypes
open import synthetic-homotopy-theory.free-loops
open import synthetic-homotopy-theory.morphisms-descent-data-circle
open import synthetic-homotopy-theory.sections-descent-circle
open import synthetic-homotopy-theory.universal-property-circle
```

</details>

## Idea

Given two families `A, B : 𝕊¹ → 𝒰` over the
[circle](synthetic-homotopy-theory.circle.md), to show that they are
[equivalent](foundation.equivalences.md) is the same as showing that their
[descent data](synthetic-homotopy-theory.descent-circle.md) is equivalent.

## Definitions

### Dependent descent data for being an equivalence of families over the circle

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-descent-data-circle l l3)
  where

  family-dependent-descent-data-circle-is-equiv :
    ( t : S) → family-descent-data-circle-function-type l A B t →
    UU (l2 ⊔ l3)
  family-dependent-descent-data-circle-is-equiv t = is-equiv

  dependent-descent-data-circle-is-equiv :
    dependent-descent-data-circle
      ( l2 ⊔ l3)
      ( descent-data-circle-function-type l A B)
  pr1 dependent-descent-data-circle-is-equiv = is-equiv
  pr2 dependent-descent-data-circle-is-equiv f =
    equiv-is-equiv-left-factor
      ( aut-family-with-descent-data-circle B) ∘e
    ( equiv-is-equiv-right-factor
      ( inv-equiv (aut-family-with-descent-data-circle A)))
```

## Properties

### Characterization of dependent descent data for being an equivalence of families over the circle

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-descent-data-circle l l3)
  where

  eq-dependent-descent-data-circle-is-equiv :
    equiv-dependent-descent-data-circle
      ( descent-data-circle-function-type l A B)
      ( dependent-descent-data-circle-is-equiv l A B)
      ( dependent-descent-data-double-family-circle l
        ( family-with-descent-data-circle-function-type l A B)
        ( family-dependent-descent-data-circle-is-equiv l A B))
  pr1 eq-dependent-descent-data-circle-is-equiv f =
    equiv-is-equiv-left-factor
      ( equiv-family-with-descent-data-circle B) ∘e
    ( equiv-is-equiv-right-factor
      ( inv-equiv (equiv-family-with-descent-data-circle A)))
  pr2 eq-dependent-descent-data-circle-is-equiv f p =
    center (is-property-is-equiv _ _ _)

  family-with-dependent-descent-data-circle-is-equiv :
    double-family-with-dependent-descent-data-circle l
      ( family-with-descent-data-circle-function-type l A B)
      ( l2 ⊔ l3)
  pr1 family-with-dependent-descent-data-circle-is-equiv =
    family-dependent-descent-data-circle-is-equiv l A B
  pr1 (pr2 family-with-dependent-descent-data-circle-is-equiv) =
    dependent-descent-data-circle-is-equiv l A B
  pr2 (pr2 family-with-dependent-descent-data-circle-is-equiv) =
    eq-dependent-descent-data-circle-is-equiv
```

### Characterization of descent data for families of equivalence types over the circle

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-descent-data-circle l l3)
  where

  family-with-descent-data-circle-equivalence-type :
    family-with-descent-data-circle l (l2 ⊔ l3)
  family-with-descent-data-circle-equivalence-type =
    family-with-descent-data-circle-dependent-pair-type l
      ( family-with-descent-data-circle-function-type l A B)
      ( family-with-dependent-descent-data-circle-is-equiv l A B)
```

### A family of equivalences between families over the circle is given by an equivalence of the corresponding descent data

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-descent-data-circle l l3)
  where

  equiv-section-descent-data-circle-equiv-equiv-descent-data-circle :
    dependent-universal-property-circle l →
    ( ( t : S) →
      ( family-family-with-descent-data-circle A t) ≃
      ( family-family-with-descent-data-circle B t)) ≃
    ( equiv-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( descent-data-family-with-descent-data-circle B))
  equiv-section-descent-data-circle-equiv-equiv-descent-data-circle dup-circle =
    equivalence-reasoning
    ( ( t : S) →
        family-family-with-descent-data-circle A t ≃
        family-family-with-descent-data-circle B t)
    ≃ Σ ( fixpoint-descent-data-circle
          ( descent-data-circle-function-type l A B))
        ( λ x → is-equiv (pr1 x))
      by
      equiv-section-descent-data-circle-subtype-fixpoint-in-subtype l
        ( family-with-descent-data-circle-function-type l A B)
        ( family-with-dependent-descent-data-circle-is-equiv l A B)
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
    ≃ equiv-descent-data-circle
        ( descent-data-family-with-descent-data-circle A)
        ( descent-data-family-with-descent-data-circle B)
      by
      compute-equiv-descent-data-circle
        ( descent-data-family-with-descent-data-circle A)
        ( descent-data-family-with-descent-data-circle B)
```
