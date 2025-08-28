# Cauchy composition of species of types in subuniverses

```agda
module species.cauchy-composition-species-of-types-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.global-subuniverses
open import foundation.homotopies
open import foundation.propositions
open import foundation.relaxed-sigma-decompositions
open import foundation.sigma-closed-subuniverses
open import foundation.sigma-decomposition-subuniverse
open import foundation.subuniverses
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import species.cauchy-composition-species-of-types
open import species.species-of-types-in-subuniverses
open import species.unit-cauchy-composition-species-of-types
open import species.unit-cauchy-composition-species-of-types-in-subuniverses
```

</details>

## Idea

A [species](species.species-of-types-in-subuniverses.md)
`S : type-subuniverse P → type-subuniverse Q` induces its
[Cauchy series](species.cauchy-series-species-of-types-in-subuniverses.md)

```text
  X ↦ Σ (A : type-subuniverse P), (S A) × (A → X)
```

The
{{#concept "Cauchy composition" Disambiguation="of species of types in a subuniverse" Agda=cauchy-composition-species-subuniverse}}
of species `S` and `T` is obtained from the coefficients of the composite of the
Cauchy series of `S` and `T`.

## Definition

### Cauchy composition of species

```agda
module _
  {l1 l2 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse (λ l → l))
  where

  type-cauchy-composition-species-subuniverse :
    {l3 l4 : Level} →
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l3)) →
    (T : species-subuniverse P (subuniverse-global-subuniverse Q l4)) →
    type-subuniverse P → UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
  type-cauchy-composition-species-subuniverse {l3} {l4} S T X =
    Σ ( Σ-Decomposition-Subuniverse P X)
      ( λ D →
        ( inclusion-subuniverse
          ( subuniverse-global-subuniverse Q l3)
          ( S (subuniverse-indexing-type-Σ-Decomposition-Subuniverse P X D))) ×
        ( (x : indexing-type-Σ-Decomposition-Subuniverse P X D) →
          inclusion-subuniverse
          ( subuniverse-global-subuniverse Q l4)
          ( T (subuniverse-cotype-Σ-Decomposition-Subuniverse P X D x))))

  is-closed-under-cauchy-composition-species-subuniverse : UUω
  is-closed-under-cauchy-composition-species-subuniverse =
    { l3 l4 : Level}
    ( S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
    ( T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
    ( X : type-subuniverse P) →
    is-in-global-subuniverse Q
      ( type-cauchy-composition-species-subuniverse S T X)

module _
  {l1 l2 l3 l4 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse (λ l → l))
  (C1 : is-closed-under-cauchy-composition-species-subuniverse P Q)
  (C2 : is-closed-under-Σ-subuniverse P)
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  where

  cauchy-composition-species-subuniverse :
    species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
  cauchy-composition-species-subuniverse X =
    ( type-cauchy-composition-species-subuniverse P Q S T X , C1 S T X)
```

## Properties

### Σ-extension of species of types in a subuniverse preserves cauchy composition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse (λ l → l))
  (C1 : is-closed-under-cauchy-composition-species-subuniverse P Q)
  (C2 : is-closed-under-Σ-subuniverse P)
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  where

  preserves-cauchy-composition-Σ-extension-species-subuniverse :
    ( X : UU l1) →
    Σ-extension-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
      ( cauchy-composition-species-subuniverse P Q C1 C2 S T)
      ( X) ≃
    ( cauchy-composition-species-types
      ( Σ-extension-species-subuniverse P
        ( subuniverse-global-subuniverse Q l3)
        ( S))
      ( Σ-extension-species-subuniverse P
        ( subuniverse-global-subuniverse Q l4)
        ( T))
      ( X))
  preserves-cauchy-composition-Σ-extension-species-subuniverse X =
    ( equiv-tot
      ( λ D →
        ( equiv-product-right inv-distributive-Π-Σ) ∘e
        ( inv-equiv right-distributive-product-Σ) ∘e
        ( equiv-tot (λ _ → inv-equiv left-distributive-product-Σ)) ∘e
        ( associative-Σ _ _ _))) ∘e
    ( associative-Σ _ _ _) ∘e
    ( equiv-Σ-equiv-base
      ( _)
      ( ( equiv-remove-redundant-prop
          ( is-prop-type-Prop (P X))
          ( λ D →
            ( tr
              ( is-in-subuniverse P)
              ( eq-equiv
                ( inv-equiv
                  ( matching-correspondence-Relaxed-Σ-Decomposition (pr1 D))))
              ( C2
                  ( indexing-type-Relaxed-Σ-Decomposition (pr1 D) , pr1 (pr2 D))
                  ( λ x →
                    ( cotype-Relaxed-Σ-Decomposition (pr1 D) x ,
                      pr2 (pr2 D) x)))))) ∘e
        ( commutative-product) ∘e
        ( equiv-tot
          ( λ p → equiv-total-is-in-subuniverse-Σ-Decomposition P (X , p))))) ∘e
    ( inv-associative-Σ _ _ _)
```

### Unit laws for Cauchy composition of species-subuniverse

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (Q : global-subuniverse (λ l → l))
  ( C3 : is-in-subuniverse P (raise-unit l1))
  ( C4 :
    is-closed-under-is-contr-subuniverses P
      ( subuniverse-global-subuniverse Q l1))
  (X : UU l1)
  where

  map-equiv-Σ-extension-cauchy-composition-unit-subuniverse :
    Σ-extension-species-subuniverse P
      ( subuniverse-global-subuniverse Q l1)
      ( cauchy-composition-unit-species-subuniverse P Q C4)
      ( X) →
    unit-species-types X
  map-equiv-Σ-extension-cauchy-composition-unit-subuniverse (p , H) = H

  map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverse :
    unit-species-types X →
    Σ-extension-species-subuniverse P
      ( subuniverse-global-subuniverse Q l1)
      ( cauchy-composition-unit-species-subuniverse P Q C4)
      ( X)
  pr1 (map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverse H) =
    is-in-subuniverse-equiv P (equiv-is-contr is-contr-raise-unit H) C3
  pr2 (map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverse H) = H

  is-section-map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverse :
    ( map-equiv-Σ-extension-cauchy-composition-unit-subuniverse ∘
      map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverse) ~ id
  is-section-map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverse =
    refl-htpy

  is-retraction-map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverse :
    ( map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverse ∘
      map-equiv-Σ-extension-cauchy-composition-unit-subuniverse) ~ id
  is-retraction-map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverse
    x =
    eq-pair
      ( eq-is-prop (is-prop-type-Prop (P X)))
      ( eq-is-prop is-property-is-contr)

  is-equiv-map-equiv-Σ-extension-cauchy-composition-unit-subuniverse :
    is-equiv map-equiv-Σ-extension-cauchy-composition-unit-subuniverse
  is-equiv-map-equiv-Σ-extension-cauchy-composition-unit-subuniverse =
    is-equiv-is-invertible
      map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverse
      is-section-map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverse
      is-retraction-map-inv-equiv-Σ-extension-cauchy-composition-unit-subuniverse

  equiv-Σ-extension-cauchy-composition-unit-subuniverse :
    Σ-extension-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q l1)
      ( cauchy-composition-unit-species-subuniverse P Q C4)
      ( X) ≃
    unit-species-types X
  pr1 equiv-Σ-extension-cauchy-composition-unit-subuniverse =
    map-equiv-Σ-extension-cauchy-composition-unit-subuniverse
  pr2 equiv-Σ-extension-cauchy-composition-unit-subuniverse =
    is-equiv-map-equiv-Σ-extension-cauchy-composition-unit-subuniverse

module _
  { l1 l2 l3 : Level}
  ( P : subuniverse l1 l2)
  ( Q : global-subuniverse (λ l → l))
  ( C1 : is-closed-under-cauchy-composition-species-subuniverse P Q)
  ( C2 : is-closed-under-Σ-subuniverse P)
  ( C3 : is-in-subuniverse P (raise-unit l1))
  ( C4 :
    is-closed-under-is-contr-subuniverses P
      ( subuniverse-global-subuniverse Q l1))
  ( S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  where

  equiv-left-unit-law-cauchy-composition-species-subuniverse :
    ( X : type-subuniverse P) →
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
      ( cauchy-composition-species-subuniverse P Q C1 C2
        ( cauchy-composition-unit-species-subuniverse P Q C4)
        ( S)
        ( X)) ≃
    inclusion-subuniverse (subuniverse-global-subuniverse Q l3) (S X)
  equiv-left-unit-law-cauchy-composition-species-subuniverse X =
    ( inv-equiv
      ( equiv-Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l3)
        ( S)
        ( X))) ∘e
    ( left-unit-law-cauchy-composition-species-types
      ( Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l3)
        ( S))
      ( inclusion-subuniverse P X)) ∘e
    ( equiv-tot
      ( λ D →
        equiv-product-left
          ( equiv-Σ-extension-cauchy-composition-unit-subuniverse
            ( P)
            ( Q)
            ( C3)
            ( C4)
            ( indexing-type-Relaxed-Σ-Decomposition D)))) ∘e
    ( preserves-cauchy-composition-Σ-extension-species-subuniverse P Q C1 C2
      ( cauchy-composition-unit-species-subuniverse P Q C4)
      ( S)
      ( inclusion-subuniverse P X)) ∘e
    ( equiv-Σ-extension-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
      ( cauchy-composition-species-subuniverse P Q C1 C2
        ( cauchy-composition-unit-species-subuniverse P Q C4)
        ( S))
      ( X))

  equiv-right-unit-law-cauchy-composition-species-subuniverse :
    ( X : type-subuniverse P) →
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
      ( cauchy-composition-species-subuniverse P Q C1 C2 S
        ( cauchy-composition-unit-species-subuniverse P Q C4)
        ( X)) ≃
    inclusion-subuniverse (subuniverse-global-subuniverse Q l3) (S X)
  equiv-right-unit-law-cauchy-composition-species-subuniverse X =
    ( inv-equiv
      ( equiv-Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l3)
        ( S)
        ( X))) ∘e
    ( right-unit-law-cauchy-composition-species-types
        ( Σ-extension-species-subuniverse
          ( P)
          ( subuniverse-global-subuniverse Q l3)
          ( S))
        ( inclusion-subuniverse P X)) ∘e
    ( equiv-tot
      ( λ D →
        equiv-product-right
          ( equiv-Π-equiv-family
            ( λ x →
              equiv-Σ-extension-cauchy-composition-unit-subuniverse P Q C3 C4
                ( cotype-Relaxed-Σ-Decomposition D x))))) ∘e
    ( preserves-cauchy-composition-Σ-extension-species-subuniverse P Q C1 C2 S
      ( cauchy-composition-unit-species-subuniverse P Q C4)
      ( inclusion-subuniverse P X)) ∘e
    ( equiv-Σ-extension-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
      ( cauchy-composition-species-subuniverse P Q C1 C2 S
        ( cauchy-composition-unit-species-subuniverse P Q C4))
      ( X))
```

### Associativity of composition of species of types in subuniverse

```agda
module _
  { l1 l2 l3 l4 l5 : Level}
  ( P : subuniverse l1 l2)
  ( Q : global-subuniverse (λ l → l))
  ( C1 : is-closed-under-cauchy-composition-species-subuniverse P Q)
  ( C2 : is-closed-under-Σ-subuniverse P)
  ( S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  ( T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  ( U : species-subuniverse P (subuniverse-global-subuniverse Q l5))
  where

  equiv-associative-cauchy-composition-species-subuniverse :
    (X : type-subuniverse P) →
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
      ( cauchy-composition-species-subuniverse P Q C1 C2 S
        ( cauchy-composition-species-subuniverse P Q C1 C2 T U)
        ( X)) ≃
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
      ( cauchy-composition-species-subuniverse P Q C1 C2
        ( cauchy-composition-species-subuniverse P Q C1 C2 S T)
        ( U)
        ( X))
  equiv-associative-cauchy-composition-species-subuniverse X =
    ( inv-equiv
      ( equiv-Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
        ( cauchy-composition-species-subuniverse P Q C1 C2
          ( cauchy-composition-species-subuniverse P Q C1 C2 S T)
          ( U))
        ( X))) ∘e
    ( inv-equiv
      ( preserves-cauchy-composition-Σ-extension-species-subuniverse P Q C1 C2
        ( cauchy-composition-species-subuniverse P Q C1 C2 S T)
        ( U)
        ( inclusion-subuniverse P X))) ∘e
    ( equiv-tot
      ( λ D →
        equiv-product-left
          ( inv-equiv
            ( preserves-cauchy-composition-Σ-extension-species-subuniverse
              ( P)
              ( Q)
              ( C1)
              ( C2)
              ( S)
              ( T)
              ( indexing-type-Relaxed-Σ-Decomposition D))))) ∘e
    ( equiv-associative-cauchy-composition-species-types
      ( Σ-extension-species-subuniverse P
        ( subuniverse-global-subuniverse Q l3)
        ( S))
      ( Σ-extension-species-subuniverse P
        ( subuniverse-global-subuniverse Q l4)
        ( T))
      ( Σ-extension-species-subuniverse P
        ( subuniverse-global-subuniverse Q l5)
        ( U))
      ( inclusion-subuniverse P X)) ∘e
    ( equiv-tot
      ( λ D →
        equiv-product-right
          ( equiv-Π-equiv-family
            ( λ y →
              preserves-cauchy-composition-Σ-extension-species-subuniverse
                ( P)
                ( Q)
                ( C1)
                ( C2)
                ( T)
                ( U)
                ( cotype-Relaxed-Σ-Decomposition D y))))) ∘e
    ( preserves-cauchy-composition-Σ-extension-species-subuniverse P Q C1 C2 S
      ( cauchy-composition-species-subuniverse P Q C1 C2 T U)
      ( inclusion-subuniverse P X)) ∘e
    ( equiv-Σ-extension-species-subuniverse P
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
      ( cauchy-composition-species-subuniverse P Q C1 C2 S
        ( cauchy-composition-species-subuniverse P Q C1 C2 T U))
      ( X))
```
