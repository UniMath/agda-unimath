# Small Composition of species of finite inhabited types

```agda
{-# OPTIONS --lossy-unification #-}

module species.small-cauchy-composition-species-of-finite-inhabited-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.decidable-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.relaxed-sigma-decompositions
open import foundation.sigma-closed-subuniverses
open import foundation.sigma-decomposition-subuniverse
open import foundation.subuniverses
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.unit-type
open import foundation.universe-levels

open import species.small-cauchy-composition-species-of-types-in-subuniverses
open import species.species-of-finite-inhabited-types

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.decidable-propositions
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
open import univalent-combinatorics.sigma-decompositions
open import univalent-combinatorics.small-types
```

</details>

## Definition

```agda
equiv-Σ-Decomposition-Inhabited-Finite-Type-Σ-Decomposition-Finite-Type :
  {l : Level} (X : Inhabited-Finite-Type l) →
  Σ-Decomposition-Finite-Type l l (finite-type-Inhabited-Finite-Type X) ≃
  Σ-Decomposition-Subuniverse
    ( is-finite-and-inhabited-Prop)
    ( map-compute-Inhabited-Finite-Type' X)
equiv-Σ-Decomposition-Inhabited-Finite-Type-Σ-Decomposition-Finite-Type X =
  ( inv-equiv
    ( equiv-total-is-in-subuniverse-Σ-Decomposition
      ( is-finite-and-inhabited-Prop)
      ( map-compute-Inhabited-Finite-Type' X))) ∘e
  ( ( equiv-tot
      ( λ D →
        equiv-product-left
          ( equiv-add-redundant-prop
            ( is-property-is-inhabited _)
            ( λ _ →
              map-is-inhabited
                ( pr1 ∘ map-matching-correspondence-Relaxed-Σ-Decomposition D)
                ( is-inhabited-type-Inhabited-Finite-Type X))))) ∘e
    ( ( equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-Finite-Type
        ( finite-type-Inhabited-Finite-Type X))))

is-finite-Σ-Decomposition-Subuniverse-Inhabited-Finite-Type :
  {l : Level} (X : Inhabited-Finite-Type l) →
  is-finite
    ( Σ-Decomposition-Subuniverse
      ( is-finite-and-inhabited-Prop {l})
      ( map-compute-Inhabited-Finite-Type' X))
is-finite-Σ-Decomposition-Subuniverse-Inhabited-Finite-Type X =
  is-finite-equiv
    ( equiv-Σ-Decomposition-Inhabited-Finite-Type-Σ-Decomposition-Finite-Type X)
    ( is-finite-Σ-Decomposition-Finite-Type
      ( finite-type-Inhabited-Finite-Type X))

finite-Σ-Decomposition-Subuniverse-Inhabited-Finite-Type :
  {l : Level} (X : Inhabited-Finite-Type l) → Finite-Type (lsuc l)
pr1 (finite-Σ-Decomposition-Subuniverse-Inhabited-Finite-Type X) =
  Σ-Decomposition-Subuniverse
    ( is-finite-and-inhabited-Prop)
    ( map-compute-Inhabited-Finite-Type' X)
pr2 (finite-Σ-Decomposition-Subuniverse-Inhabited-Finite-Type X) =
  is-finite-Σ-Decomposition-Subuniverse-Inhabited-Finite-Type X

module _
  {l1 l2 : Level}
  where

  finite-small-cauchy-composition-species-subuniverse :
    (S T : species-Inhabited-Finite-Type l1 (l1 ⊔ l2))
    (X : Inhabited-Finite-Type l1) →
    Finite-Type (lsuc l1 ⊔ l2)
  finite-small-cauchy-composition-species-subuniverse S T X =
    Σ-Finite-Type
      ( finite-Σ-Decomposition-Subuniverse-Inhabited-Finite-Type X)
      ( λ D →
        product-Finite-Type
          ( S ( subuniverse-indexing-type-Σ-Decomposition-Subuniverse
                ( is-finite-and-inhabited-Prop)
                ( map-compute-Inhabited-Finite-Type' X)
                ( D)))
          ( Π-Finite-Type
            ( finite-type-Inhabited-Finite-Type
              ( map-inv-compute-Inhabited-Finite-Type'
                ( subuniverse-indexing-type-Σ-Decomposition-Subuniverse
                  ( is-finite-and-inhabited-Prop)
                  ( map-compute-Inhabited-Finite-Type' X)
                  ( D))))
            ( λ x →
              T ( subuniverse-cotype-Σ-Decomposition-Subuniverse
                  ( is-finite-and-inhabited-Prop)
                  ( map-compute-Inhabited-Finite-Type' X)
                  ( D)
                  ( x)))))

  private
    C1 :
      ( S T : species-Inhabited-Finite-Type l1 (l1 ⊔ l2)) →
      ( X : type-subuniverse is-finite-and-inhabited-Prop) →
      is-small
        (l1 ⊔ l2)
        ( small-cauchy-composition-species-subuniverse'
          is-finite-and-inhabited-Prop
          is-finite-Prop
          S T X)
    C1 S T X =
      is-small-is-finite
        (l1 ⊔ l2)
        ( finite-small-cauchy-composition-species-subuniverse S T
          (map-inv-compute-Inhabited-Finite-Type' X))

    C2 :
      ( S T : species-Inhabited-Finite-Type l1 (l1 ⊔ l2)) →
      (X : type-subuniverse is-finite-and-inhabited-Prop) →
      is-finite (type-is-small (C1 S T X))
    C2 S T X =
      is-finite-equiv
        ( equiv-is-small (C1 S T X))
        ( is-finite-type-Finite-Type
          ( finite-small-cauchy-composition-species-subuniverse
            ( S)
            ( T)
            ( map-inv-compute-Inhabited-Finite-Type' X)))

    C3 : is-closed-under-Σ-subuniverse (is-finite-and-inhabited-Prop {l1})
    C3 X Y =
      is-finite-Σ
        ( is-finite-Inhabited-Finite-Type
          ( map-inv-compute-Inhabited-Finite-Type' X))
        ( λ x →
          is-finite-Inhabited-Finite-Type
            ( map-inv-compute-Inhabited-Finite-Type' (Y x))) ,
      is-inhabited-Σ
        ( is-inhabited-type-Inhabited-Finite-Type
          ( map-inv-compute-Inhabited-Finite-Type' X))
        ( λ x → is-inhabited-type-Inhabited-Finite-Type
          ( map-inv-compute-Inhabited-Finite-Type' (Y x)))

    C4 : is-finite-and-inhabited (raise-unit l1)
    C4 =
      is-finite-is-contr is-contr-raise-unit ,
      is-inhabited-is-contr is-contr-raise-unit

    C5 : (X : UU l1) → is-small (l1 ⊔ l2) (is-contr X)
    C5 X = is-small-lmax l2 (is-contr X)

    C6 :
      ( X : type-subuniverse {l1} is-finite-and-inhabited-Prop) →
      ( is-finite
        ( type-is-small
            ( C5 ( inclusion-subuniverse is-finite-and-inhabited-Prop X))))
    C6 X =
      is-finite-is-decidable-Prop
        ( _ ,
          is-prop-equiv
            ( inv-equiv
              ( equiv-is-small
                ( is-small-lmax l2
                  ( is-contr
                    ( type-Inhabited-Finite-Type
                      ( map-inv-compute-Inhabited-Finite-Type' X))))))
                ( is-property-is-contr))
        ( is-decidable-equiv
          ( inv-equiv
            ( equiv-is-small
              ( is-small-lmax
                ( l2)
                ( is-contr
                  ( type-Inhabited-Finite-Type
                    ( map-inv-compute-Inhabited-Finite-Type' X))))))
          ( is-decidable-is-contr-is-finite
            ( is-finite-Inhabited-Finite-Type
              ( map-inv-compute-Inhabited-Finite-Type' X))))

  small-cauchy-composition-species-Inhabited-Finite-Type :
    species-Inhabited-Finite-Type l1 (l1 ⊔ l2) →
    species-Inhabited-Finite-Type l1 (l1 ⊔ l2) →
    species-Inhabited-Finite-Type l1 (l1 ⊔ l2)
  small-cauchy-composition-species-Inhabited-Finite-Type =
    small-cauchy-composition-species-subuniverse
      is-finite-and-inhabited-Prop
      is-finite-Prop
      C1 C2 C3

  small-cauchy-composition-unit-species-Inhabited-Finite-Type :
    species-Inhabited-Finite-Type l1 (l1 ⊔ l2)
  small-cauchy-composition-unit-species-Inhabited-Finite-Type =
    small-cauchy-composition-unit-species-subuniverse
      is-finite-and-inhabited-Prop
      is-finite-Prop
      C1 C2 C3 C4 C5 C6

  left-unit-law-small-cauchy-composition-species-Inhabited-Finite-Type :
    ( S : species-Inhabited-Finite-Type l1 (l1 ⊔ l2)) →
    small-cauchy-composition-species-Inhabited-Finite-Type
      small-cauchy-composition-unit-species-Inhabited-Finite-Type
      S ＝
    S
  left-unit-law-small-cauchy-composition-species-Inhabited-Finite-Type =
    left-unit-law-small-cauchy-composition-species-subuniverse
      is-finite-and-inhabited-Prop
      is-finite-Prop
      C1 C2 C3 C4 C5 C6

  right-unit-law-small-cauchy-composition-species-Inhabited-Finite-Type :
    ( S : species-Inhabited-Finite-Type l1 (l1 ⊔ l2)) →
    small-cauchy-composition-species-Inhabited-Finite-Type
      S
      small-cauchy-composition-unit-species-Inhabited-Finite-Type ＝
    S
  right-unit-law-small-cauchy-composition-species-Inhabited-Finite-Type =
    right-unit-law-small-cauchy-composition-species-subuniverse
      is-finite-and-inhabited-Prop
      is-finite-Prop
      C1 C2 C3 C4 C5 C6

  associative-small-cauchy-composition-species-Inhabited-Finite-Type :
    (S T U : species-Inhabited-Finite-Type l1 (l1 ⊔ l2)) →
    small-cauchy-composition-species-Inhabited-Finite-Type
      ( S)
      ( small-cauchy-composition-species-Inhabited-Finite-Type T U) ＝
    small-cauchy-composition-species-Inhabited-Finite-Type
      ( small-cauchy-composition-species-Inhabited-Finite-Type S T)
      ( U)
  associative-small-cauchy-composition-species-Inhabited-Finite-Type =
    associative-small-cauchy-composition-species-subuniverse
      is-finite-and-inhabited-Prop
      is-finite-Prop
      C1 C2 C3
```
