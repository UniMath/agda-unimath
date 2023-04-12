# Cauchy composition of species of subuniverse

```agda
module species.cauchy-composition-species-of-types-in-subuniverse where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.relaxed-sigma-decompositions
open import foundation.sigma-decomposition-subuniverse
open import foundation.subuniverses
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import species.cauchy-composition-species-of-types
open import species.species-of-types-in-subuniverse
```

</details>

## Idea

A species `S : Inhabited-Type → UU l` can be thought of as the analytic
endofunctor

```md
  X ↦ Σ (A : Inhabited-Type) (S A) × (A → X)
```

Using the formula for composition of analytic endofunctors, we obtain a way to
compose species.

## Definition

### Cauchy composition of species

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : subuniverse l1 l2 )
  (Q : global-subuniverse id)
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  where

  cauchy-composition-species-subuniverse' :
    type-subuniverse P → UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cauchy-composition-species-subuniverse' X =
    Σ ( Σ-Decomposition-subuniverse P X)
      ( λ D →
        ( inclusion-subuniverse
          ( subuniverse-global-subuniverse Q l3)
          ( S (subuniverse-indexing-type-Σ-Decomposition-subuniverse P X D))) ×
        ( (x : indexing-type-Σ-Decomposition-subuniverse P X D ) →
          inclusion-subuniverse
          ( subuniverse-global-subuniverse Q l4)
          ( T (subuniverse-cotype-Σ-Decomposition-subuniverse P X D x))))

module _
  {l1 l2 l3 l4 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse id)
  (C1 :
    {l5 l6 : Level}
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l5))
    (T : species-subuniverse P (subuniverse-global-subuniverse Q l6))
    (X : type-subuniverse P) →
    is-in-subuniverse
      (subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l5 ⊔ l6))
      (cauchy-composition-species-subuniverse' P Q S T X))
  (C2 :
    ( ( X : type-subuniverse P) →
      ( Y : (inclusion-subuniverse P X) → type-subuniverse P) →
      is-in-subuniverse P
        ( Σ (inclusion-subuniverse P X) (λ x → inclusion-subuniverse P (Y x)))))
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  where

  cauchy-composition-species-subuniverse :
    species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
  cauchy-composition-species-subuniverse X =
    cauchy-composition-species-subuniverse' P Q S T X , C1 S T X
```

## Properties

### Equivalent form with species of types

```agda
  equiv-cauchy-composition-Σ-extension-species-subuniverse :
    ( X : UU l1) →
    Σ-extension-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
      ( cauchy-composition-species-subuniverse)
      ( X) ≃
    ( cauchy-composition-species-types
      ( Σ-extension-species-subuniverse P (subuniverse-global-subuniverse Q l3) S)
      ( Σ-extension-species-subuniverse P (subuniverse-global-subuniverse Q l4) T)
      ( X))
  equiv-cauchy-composition-Σ-extension-species-subuniverse X =
    ( ( equiv-tot
        ( λ D →
          ( ( equiv-prod id-equiv (inv-equiv distributive-Π-Σ)) ∘e
          ( ( inv-equiv right-distributive-prod-Σ) ∘e
          ( ( equiv-tot (λ _ → inv-equiv (left-distributive-prod-Σ)))))) ∘e
          ( ( assoc-Σ _ _ _)))) ∘e
      ( ( assoc-Σ
          ( Relaxed-Σ-Decomposition l1 l1 X)
          ( λ D →
              is-in-subuniverse P (indexing-type-Relaxed-Σ-Decomposition D) ×
              ((x : indexing-type-Relaxed-Σ-Decomposition D) →
               is-in-subuniverse P (cotype-Relaxed-Σ-Decomposition D x)))
          ( _)) ∘e
        ( ( equiv-Σ-equiv-base
            ( _)
            ( ( inv-equiv
                ( equiv-add-redundant-prop
                  ( is-prop-type-Prop (P X))
                  ( λ D →
                    ( tr
                      ( is-in-subuniverse P)
                      ( eq-equiv
                        ( Σ (indexing-type-Relaxed-Σ-Decomposition (pr1 D))
                          (cotype-Relaxed-Σ-Decomposition (pr1 D)))
                        ( X)
                        ( inv-equiv
                          ( matching-correspondence-Relaxed-Σ-Decomposition
                              ( pr1 D))))
                      ( C2
                          ( indexing-type-Relaxed-Σ-Decomposition (pr1 D) ,
                              pr1 (pr2 D))
                          ( λ x →
                            ( cotype-Relaxed-Σ-Decomposition (pr1 D) x ,
                                pr2 (pr2 D) x)))))) ∘e
              ( commutative-prod ∘e
              ( equiv-tot
                ( λ p →
                  equiv-Relaxed-Σ-Decomposition-Σ-Decomposition-subuniverse
                    ( P)
                    (X , p))))))) ∘e
          ( ( inv-assoc-Σ
              ( is-in-subuniverse P X)
              ( λ p → Σ-Decomposition-subuniverse P (X , p))
              ( _))))))
```

### Unit laws for Cauchy composition of species-subuniverse

```agda
module _
  {l1 l2 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse id)
  (C3 : is-in-subuniverse P (raise-unit l1))
  (C4 :
    (X : type-subuniverse P) →
    is-in-subuniverse
      ( subuniverse-global-subuniverse Q l1)
      ( is-contr (inclusion-subuniverse P X)))
  where

  cauchy-composition-unit-species-subuniverse :
    species-subuniverse P (subuniverse-global-subuniverse Q l1)
  cauchy-composition-unit-species-subuniverse X =
    (is-contr (inclusion-subuniverse P X)) ,
    C4 X

  equiv-Σ-extension-cauchy-composition-unit-subuniverse :
    (X : UU l1) →
    Σ-extension-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q l1)
      ( cauchy-composition-unit-species-subuniverse)
      ( X) ≃
    cauchy-composition-unit-species-types X
  pr1 (equiv-Σ-extension-cauchy-composition-unit-subuniverse X) (p , is-contr-X) =
    is-contr-X
  pr2 (equiv-Σ-extension-cauchy-composition-unit-subuniverse X) =
    is-equiv-has-inverse
      ( λ is-contr-X →
        ( tr
            ( is-in-subuniverse P)
            ( eq-equiv
                ( raise-unit l1)
                ( X)
                ( ( inv-equiv
                      ( terminal-map ,
                        is-equiv-terminal-map-is-contr is-contr-X)) ∘e
                   inv-equiv (compute-raise-unit l1))) C3) ,
        is-contr-X)
      ( refl-htpy)
      ( λ x →
        eq-pair
          ( eq-is-prop (is-prop-type-Prop (P X)))
          ( eq-is-prop is-property-is-contr))

module _
  {l1 l2 l3 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse id)
  (C1 :
    {l5 l6 : Level}
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l5))
    (T : species-subuniverse P (subuniverse-global-subuniverse Q l6))
    (X : type-subuniverse P) →
    is-in-subuniverse
      (subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l5 ⊔ l6))
      (cauchy-composition-species-subuniverse' P Q S T X))
  (C2 :
    ( ( X : type-subuniverse P) →
      ( Y : (inclusion-subuniverse P X) → type-subuniverse P) →
      is-in-subuniverse P
        ( Σ (inclusion-subuniverse P X) (λ x → inclusion-subuniverse P (Y x)))))
  (C3 : is-in-subuniverse P (raise-unit l1))
  (C4 :
    (X : type-subuniverse P) →
    is-in-subuniverse
      ( subuniverse-global-subuniverse Q l1)
      ( is-contr (inclusion-subuniverse P X)))
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  where

  equiv-left-unit-law-cauchy-composition-species-subuniverse :
    ( X : type-subuniverse P) →
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
      ( cauchy-composition-species-subuniverse
        ( P)
        ( Q)
        ( C1)
        ( C2)
        ( cauchy-composition-unit-species-subuniverse P Q C3 C4)
        ( S) X) ≃
    inclusion-subuniverse (subuniverse-global-subuniverse Q l3) (S X)
  equiv-left-unit-law-cauchy-composition-species-subuniverse X =
    ( ( inv-equiv
        ( equiv-Σ-extension-species-subuniverse
          ( P)
          ( subuniverse-global-subuniverse Q l3)
          ( S)
          ( X) ) ) ∘e
      ( ( left-unit-law-cauchy-composition-species-types
          ( Σ-extension-species-subuniverse
            ( P)
            ( subuniverse-global-subuniverse Q l3)
            ( S))
          ( inclusion-subuniverse P X)) ∘e
        ( ( equiv-tot
            ( λ D →
              equiv-prod
                ( equiv-Σ-extension-cauchy-composition-unit-subuniverse
                  ( P)
                  ( Q)
                  ( C3)
                  ( C4)
                  ( indexing-type-Relaxed-Σ-Decomposition D))
                ( id-equiv))) ∘e
          ( ( equiv-cauchy-composition-Σ-extension-species-subuniverse
              ( P)
              ( Q)
              ( C1)
              ( C2)
              ( cauchy-composition-unit-species-subuniverse P Q C3 C4)
              ( S)
              ( inclusion-subuniverse P X)) ∘e
            ( ( equiv-Σ-extension-species-subuniverse
                ( P)
                ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
                ( cauchy-composition-species-subuniverse
                  ( P)
                  ( Q)
                  ( C1)
                  ( C2)
                  ( cauchy-composition-unit-species-subuniverse P Q C3 C4)
                  ( S))
                  ( X)))))))

  equiv-right-unit-law-cauchy-composition-species-subuniverse :
    ( X : type-subuniverse P) →
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
      ( cauchy-composition-species-subuniverse
        ( P)
        ( Q)
        ( C1)
        ( C2)
        ( S)
        ( cauchy-composition-unit-species-subuniverse P Q C3 C4)
        ( X)) ≃
    inclusion-subuniverse (subuniverse-global-subuniverse Q l3) (S X)
  equiv-right-unit-law-cauchy-composition-species-subuniverse X =
    ( ( inv-equiv
        ( equiv-Σ-extension-species-subuniverse
          ( P)
          ( subuniverse-global-subuniverse Q l3)
          ( S)
          ( X))) ∘e
      ( ( right-unit-law-cauchy-composition-species-types
          ( Σ-extension-species-subuniverse
            ( P)
            ( subuniverse-global-subuniverse Q l3)
            ( S))
          ( inclusion-subuniverse P X)) ∘e
        ( ( equiv-tot
            ( λ D →
              equiv-prod
                ( id-equiv)
                ( equiv-Π
                  ( _)
                  ( id-equiv)
                  ( λ x →
                    equiv-Σ-extension-cauchy-composition-unit-subuniverse
                      ( P)
                      ( Q)
                      ( C3)
                      ( C4)
                      ( cotype-Relaxed-Σ-Decomposition D x))))) ∘e
          ( ( equiv-cauchy-composition-Σ-extension-species-subuniverse
                ( P)
                ( Q)
                ( C1)
                ( C2)
                ( S)
                ( cauchy-composition-unit-species-subuniverse P Q C3 C4)
                ( inclusion-subuniverse P X)) ∘e
            ( ( equiv-Σ-extension-species-subuniverse
                ( P)
                ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
                ( cauchy-composition-species-subuniverse
                    ( P)
                    ( Q)
                    ( C1)
                    ( C2)
                    ( S)
                    ( cauchy-composition-unit-species-subuniverse P Q C3 C4))
                ( X)))))))
```

### Associativity of composition of species of types in subuniverse

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (P : subuniverse l1 l2)
  (Q : global-subuniverse id)
  (C1 :
    {l6 l7 : Level}
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l6))
    (T : species-subuniverse P (subuniverse-global-subuniverse Q l7))
    (X : type-subuniverse P) →
    is-in-subuniverse
      (subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l6 ⊔ l7))
      (cauchy-composition-species-subuniverse' P Q S T X))
  (C2 :
    ( ( X : type-subuniverse P) →
      ( Y : (inclusion-subuniverse P X) → type-subuniverse P) →
      is-in-subuniverse P
        ( Σ (inclusion-subuniverse P X) (λ x → inclusion-subuniverse P (Y x)))))
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l4))
  (U : species-subuniverse P (subuniverse-global-subuniverse Q l5))
  where

  equiv-assoc-cauchy-composition-species-subuniverse :
    (X : type-subuniverse P) →
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
      ( cauchy-composition-species-subuniverse
        ( P)
        ( Q)
        ( C1)
        ( C2)
        ( S)
        ( cauchy-composition-species-subuniverse P Q C1 C2 T  U)
        ( X)) ≃
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
      ( cauchy-composition-species-subuniverse
        ( P)
        ( Q)
        ( C1)
        ( C2)
        ( cauchy-composition-species-subuniverse P Q C1 C2 S T)
        ( U)
        ( X))
  equiv-assoc-cauchy-composition-species-subuniverse X =
    ( ( inv-equiv
        ( equiv-Σ-extension-species-subuniverse
          ( P)
          ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
          ( cauchy-composition-species-subuniverse P Q C1 C2
            ( cauchy-composition-species-subuniverse P Q C1 C2 S T) U)
          ( X))) ∘e
      ( ( inv-equiv
          ( equiv-cauchy-composition-Σ-extension-species-subuniverse
            ( P)
            ( Q)
            ( C1)
            ( C2)
            ( cauchy-composition-species-subuniverse P Q C1 C2 S T)
            ( U)
            ( inclusion-subuniverse P X))) ∘e
        ( ( equiv-tot
            λ D →
              equiv-prod
               ( inv-equiv
                 ( equiv-cauchy-composition-Σ-extension-species-subuniverse
                   ( P)
                   ( Q)
                   ( C1)
                   ( C2)
                   ( S)
                   ( T)
                   ( indexing-type-Relaxed-Σ-Decomposition D)))
               ( id-equiv) ) ∘e
          ( ( equiv-assoc-cauchy-composition-species-types
              ( Σ-extension-species-subuniverse
                ( P)
                ( subuniverse-global-subuniverse Q l3)
                ( S))
              ( Σ-extension-species-subuniverse
                ( P)
                ( subuniverse-global-subuniverse Q l4)
                ( T))
              ( Σ-extension-species-subuniverse
                ( P)
                ( subuniverse-global-subuniverse Q l5)
                ( U))
              ( inclusion-subuniverse P X)) ∘e
            ( ( equiv-tot
                ( λ D →
                  equiv-prod
                    ( id-equiv)
                    ( equiv-Π
                      ( λ y →
                        ( cauchy-composition-species-types
                          ( Σ-extension-species-subuniverse
                            ( P)
                            ( subuniverse-global-subuniverse Q l4)
                            ( T))
                          ( Σ-extension-species-subuniverse
                            ( P)
                            ( subuniverse-global-subuniverse Q l5)
                            ( U))
                          ( cotype-Relaxed-Σ-Decomposition D y)))
                      ( id-equiv)
                      ( λ y →
                        ( equiv-cauchy-composition-Σ-extension-species-subuniverse
                          ( P)
                          ( Q)
                          ( C1)
                          ( C2)
                          ( T)
                          ( U)
                          ( cotype-Relaxed-Σ-Decomposition D y)))))) ∘e
              ( ( equiv-cauchy-composition-Σ-extension-species-subuniverse
                  ( P)
                  ( Q)
                  ( C1)
                  ( C2)
                  ( S)
                  ( cauchy-composition-species-subuniverse P Q C1 C2 T U)
                  ( inclusion-subuniverse P X) ) ∘e
                ( ( equiv-Σ-extension-species-subuniverse
                    ( P)
                    ( subuniverse-global-subuniverse
                      ( Q)
                      ( lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5))
                    ( cauchy-composition-species-subuniverse
                      ( P)
                      ( Q)
                      ( C1)
                      ( C2)
                      ( S)
                      ( cauchy-composition-species-subuniverse P Q C1 C2 T U))
                    ( X)))))))))
```
