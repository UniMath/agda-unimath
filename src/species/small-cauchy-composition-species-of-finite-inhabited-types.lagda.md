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
equiv-Σ-Decomposition-Inhabited-𝔽-Σ-Decomposition-𝔽 :
  {l : Level} (X : Inhabited-𝔽 l) →
  Σ-Decomposition-𝔽 l l (finite-type-Inhabited-𝔽 X) ≃
  Σ-Decomposition-Subuniverse
    ( is-finite-and-inhabited-Prop)
    ( map-compute-Inhabited-𝔽' X)
equiv-Σ-Decomposition-Inhabited-𝔽-Σ-Decomposition-𝔽 X =
  ( inv-equiv
    ( equiv-total-is-in-subuniverse-Σ-Decomposition
      ( is-finite-and-inhabited-Prop)
      ( map-compute-Inhabited-𝔽' X))) ∘e
  ( ( equiv-tot
      ( λ D →
        equiv-prod
          ( equiv-add-redundant-prop
            ( is-property-is-inhabited _)
            ( λ _ →
              map-is-inhabited
                ( pr1 ∘ map-matching-correspondence-Relaxed-Σ-Decomposition D)
                ( is-inhabited-type-Inhabited-𝔽 X)))
          ( id-equiv))) ∘e
    ( ( equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-𝔽
        (finite-type-Inhabited-𝔽 X))))

is-finite-Σ-Decomposition-Subuniverse-Inhabited-𝔽 :
  {l : Level} (X : Inhabited-𝔽 l) →
  is-finite
    ( Σ-Decomposition-Subuniverse
      ( is-finite-and-inhabited-Prop {l})
      ( map-compute-Inhabited-𝔽' X))
is-finite-Σ-Decomposition-Subuniverse-Inhabited-𝔽 X =
  is-finite-equiv
    ( equiv-Σ-Decomposition-Inhabited-𝔽-Σ-Decomposition-𝔽 X)
    ( is-finite-Σ-Decomposition-𝔽 (finite-type-Inhabited-𝔽 X))

finite-Σ-Decomposition-Subuniverse-Inhabited-𝔽 :
  {l : Level} (X : Inhabited-𝔽 l) → 𝔽 (lsuc l)
pr1 (finite-Σ-Decomposition-Subuniverse-Inhabited-𝔽 {l} X) =
  Σ-Decomposition-Subuniverse
    ( is-finite-and-inhabited-Prop {l})
    ( map-compute-Inhabited-𝔽' X)
pr2 (finite-Σ-Decomposition-Subuniverse-Inhabited-𝔽 X) =
  is-finite-Σ-Decomposition-Subuniverse-Inhabited-𝔽 X

module _
  {l1 l2 : Level}
  where

  finite-small-cauchy-composition-species-subuniverse :
    ( S T : species-Inhabited-𝔽 l1 (l1 ⊔ l2)) (X : Inhabited-𝔽 l1) →
    𝔽 (lsuc l1 ⊔ l2)
  finite-small-cauchy-composition-species-subuniverse S T X =
    Σ-𝔽
      ( finite-Σ-Decomposition-Subuniverse-Inhabited-𝔽 X)
      ( λ D →
        prod-𝔽
          ( S ( subuniverse-indexing-type-Σ-Decomposition-Subuniverse
                ( is-finite-and-inhabited-Prop)
                ( map-compute-Inhabited-𝔽' X)
                ( D)))
          ( Π-𝔽
            ( finite-type-Inhabited-𝔽
              ( map-inv-compute-Inhabited-𝔽'
                ( subuniverse-indexing-type-Σ-Decomposition-Subuniverse
                  ( is-finite-and-inhabited-Prop)
                  ( map-compute-Inhabited-𝔽' X)
                  ( D))))
            ( λ x →
              T ( subuniverse-cotype-Σ-Decomposition-Subuniverse
                  ( is-finite-and-inhabited-Prop)
                  ( map-compute-Inhabited-𝔽' X)
                  ( D)
                  ( x)))))

  private
    C1 :
      ( S T : species-Inhabited-𝔽 l1 (l1 ⊔ l2)) →
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
          (map-inv-compute-Inhabited-𝔽' X))

    C2 :
      ( S T : species-Inhabited-𝔽 l1 (l1 ⊔ l2)) →
      (X : type-subuniverse is-finite-and-inhabited-Prop) →
      is-finite (type-is-small (C1 S T X))
    C2 S T X =
      is-finite-equiv
        ( equiv-is-small (C1 S T X))
        ( is-finite-type-𝔽
          ( finite-small-cauchy-composition-species-subuniverse
            ( S)
            ( T)
            ( map-inv-compute-Inhabited-𝔽' X)))

    C3 : is-closed-under-Σ-subuniverse (is-finite-and-inhabited-Prop {l1})
    C3 X Y =
      is-finite-Σ
        ( is-finite-Inhabited-𝔽 (map-inv-compute-Inhabited-𝔽' X))
        ( λ x →
          is-finite-Inhabited-𝔽 (map-inv-compute-Inhabited-𝔽' (Y x))) ,
      is-inhabited-Σ
        ( is-inhabited-type-Inhabited-𝔽
          ( map-inv-compute-Inhabited-𝔽' X))
        ( λ x → is-inhabited-type-Inhabited-𝔽
          ( map-inv-compute-Inhabited-𝔽' (Y x)))

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
                    ( type-Inhabited-𝔽
                      ( map-inv-compute-Inhabited-𝔽' X))))))
                ( is-property-is-contr))
        ( is-decidable-equiv
          ( inv-equiv
            ( equiv-is-small
              ( is-small-lmax
                ( l2)
                ( is-contr
                  ( type-Inhabited-𝔽
                    ( map-inv-compute-Inhabited-𝔽' X))))))
          ( is-decidable-is-contr-is-finite
            ( is-finite-Inhabited-𝔽 (map-inv-compute-Inhabited-𝔽' X))))

  small-cauchy-composition-species-Inhabited-𝔽 :
    species-Inhabited-𝔽 l1 (l1 ⊔ l2) →
    species-Inhabited-𝔽 l1 (l1 ⊔ l2) →
    species-Inhabited-𝔽 l1 (l1 ⊔ l2)
  small-cauchy-composition-species-Inhabited-𝔽 =
    small-cauchy-composition-species-subuniverse
      is-finite-and-inhabited-Prop
      is-finite-Prop
      C1 C2 C3

  small-cauchy-composition-unit-species-Inhabited-𝔽 :
    species-Inhabited-𝔽 l1 (l1 ⊔ l2)
  small-cauchy-composition-unit-species-Inhabited-𝔽 =
    small-cauchy-composition-unit-species-subuniverse
      is-finite-and-inhabited-Prop
      is-finite-Prop
      C1 C2 C3 C4 C5 C6

  left-unit-law-small-cauchy-composition-species-Inhabited-𝔽 :
    ( S : species-Inhabited-𝔽 l1 (l1 ⊔ l2)) →
    small-cauchy-composition-species-Inhabited-𝔽
      small-cauchy-composition-unit-species-Inhabited-𝔽
      S ＝
    S
  left-unit-law-small-cauchy-composition-species-Inhabited-𝔽 =
    left-unit-law-small-cauchy-composition-species-subuniverse
      is-finite-and-inhabited-Prop
      is-finite-Prop
      C1 C2 C3 C4 C5 C6

  right-unit-law-small-cauchy-composition-species-Inhabited-𝔽 :
    ( S : species-Inhabited-𝔽 l1 (l1 ⊔ l2)) →
    small-cauchy-composition-species-Inhabited-𝔽
      S
      small-cauchy-composition-unit-species-Inhabited-𝔽 ＝
    S
  right-unit-law-small-cauchy-composition-species-Inhabited-𝔽 =
    right-unit-law-small-cauchy-composition-species-subuniverse
      is-finite-and-inhabited-Prop
      is-finite-Prop
      C1 C2 C3 C4 C5 C6

  associative-small-cauchy-composition-species-Inhabited-𝔽 :
    (S T U : species-Inhabited-𝔽 l1 (l1 ⊔ l2)) →
    small-cauchy-composition-species-Inhabited-𝔽
      ( S)
      ( small-cauchy-composition-species-Inhabited-𝔽 T U) ＝
    small-cauchy-composition-species-Inhabited-𝔽
      ( small-cauchy-composition-species-Inhabited-𝔽 S T)
      ( U)
  associative-small-cauchy-composition-species-Inhabited-𝔽 =
    associative-small-cauchy-composition-species-subuniverse
      is-finite-and-inhabited-Prop
      is-finite-Prop
      C1 C2 C3
```
