# Cauchy products of species of subuniverse

```agda
module species.cauchy-product-species-of-subuniverse where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-decompositions
open import foundation.coproduct-decompositions-subuniverse
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subuniverses
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import species.cauchy-product-species-of-types
open import species.species-of-types-in-subuniverse
```

</details>

## Idea

The Cauchy product of two species of subuniverse `S` and `T` from `P` to `Q` on
`X` is defined as

```md
  Σ (k : P) (Σ (k' : P) (Σ (e : k + k' ≃ X) S(k) × T(k')))
```

If `Q` is stable by product and dependent pair type over `P` type, then the
cauchy product is also a species of subuniverse from `P` to `Q`

## Definition

```agda
module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l1) (Q : global-subuniverse id )
  where

  cauchy-product-species-subuniverse' :
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l2))
    (T : species-subuniverse P (subuniverse-global-subuniverse Q l3))
    (X : type-subuniverse P) → UU (lsuc l1 ⊔ l2 ⊔ l3)
  cauchy-product-species-subuniverse' S T X =
    Σ ( binary-coproduct-Decomposition-subuniverse P X)
      ( λ d →
        inclusion-subuniverse (subuniverse-global-subuniverse Q l2)
          ( S (left-summand-binary-coproduct-Decomposition-subuniverse P X d)) ×
        inclusion-subuniverse (subuniverse-global-subuniverse Q l3)
          ( T (right-summand-binary-coproduct-Decomposition-subuniverse P X d)))

module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l1) (Q : global-subuniverse id )
  ( C1 :
    ( (l4 l5 : Level)
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l4))
    (T : species-subuniverse P (subuniverse-global-subuniverse Q l5))
    (X : type-subuniverse P) →
      is-in-subuniverse
        ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l4 ⊔ l5))
        ( cauchy-product-species-subuniverse' P Q S T X)))
  where

  cauchy-product-species-subuniverse :
    species-subuniverse P (subuniverse-global-subuniverse Q l2) →
    species-subuniverse P (subuniverse-global-subuniverse Q l3) →
    species-subuniverse P (subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
  pr1 (cauchy-product-species-subuniverse S T X) =
    cauchy-product-species-subuniverse' P Q S T X
  pr2 (cauchy-product-species-subuniverse S T X) = C1 l2 l3 S T X
```

## Properties

### Cauchy product is associative

```agda
module _
  {l1 l2 l3 l4 : Level} (P : subuniverse l1 l1) (Q : global-subuniverse id)
  ( C1 :
      ( (l5 l6 : Level)
        (S : species-subuniverse P (subuniverse-global-subuniverse Q l5))
        (T : species-subuniverse P (subuniverse-global-subuniverse Q l6))
        (X : type-subuniverse P) →
        is-in-subuniverse
          ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l5 ⊔ l6) )
          ( cauchy-product-species-subuniverse' P Q S T X)))
  ( C2 :
    (A B : type-subuniverse P) →
    is-in-subuniverse P (inclusion-subuniverse P A + inclusion-subuniverse P B))
  where

  module _
    (S : species-subuniverse P ( subuniverse-global-subuniverse Q l2))
    (T : species-subuniverse P ( subuniverse-global-subuniverse Q l3))
    (U : species-subuniverse P ( subuniverse-global-subuniverse Q l4))
    (X : type-subuniverse P)
    where

    equiv-left-iterated-cauchy-product-species-subuniverse :
      cauchy-product-species-subuniverse' P Q
        ( cauchy-product-species-subuniverse P Q C1 S T)
        ( U)
        ( X) ≃
      Σ ( ternary-coproduct-Decomposition-subuniverse P X)
        ( λ d →
          inclusion-subuniverse ( subuniverse-global-subuniverse Q l2)
            ( S (first-summand-ternary-coproduct-Decomposition-subuniverse P X d)) ×
            ( inclusion-subuniverse ( subuniverse-global-subuniverse Q l3)
              ( T (second-summand-ternary-coproduct-Decomposition-subuniverse P X d)) ×
              inclusion-subuniverse ( subuniverse-global-subuniverse Q l4)
              ( U (third-summand-ternary-coproduct-Decomposition-subuniverse P X d))))
    equiv-left-iterated-cauchy-product-species-subuniverse =
      ( ( equiv-Σ
          ( λ d →
            inclusion-subuniverse ( subuniverse-global-subuniverse Q l2)
            ( S (first-summand-ternary-coproduct-Decomposition-subuniverse P X d)) ×
            ( inclusion-subuniverse ( subuniverse-global-subuniverse Q l3)
              ( T (second-summand-ternary-coproduct-Decomposition-subuniverse P X d)) ×
              inclusion-subuniverse ( subuniverse-global-subuniverse Q l4)
              ( U (third-summand-ternary-coproduct-Decomposition-subuniverse P X d)))))
          ( ( equiv-Σ
              ( _)
              ( assoc-prod _ _ _ ∘e commutative-prod)
              ( λ x →
                equiv-postcomp-equiv
                  ( ( ( assoc-coprod) ∘e
                    ( ( commutative-coprod  _ _))) )
                  ( inclusion-subuniverse P X)) ∘e
              equiv-ternary-left-iterated-coproduct-Decomposition-subuniverse P X C2))
          ( λ d → assoc-prod _ _ _) ∘e
        ( ( inv-assoc-Σ
            ( binary-coproduct-Decomposition-subuniverse P X)
            ( λ z → binary-coproduct-Decomposition-subuniverse P (pr1 z))
            ( _)) ∘e
          ( ( equiv-tot  λ d → right-distributive-prod-Σ))))

    equiv-right-iterated-cauchy-product-species-subuniverse :
      cauchy-product-species-subuniverse' P Q
        ( S)
        ( cauchy-product-species-subuniverse P Q C1 T U)
        ( X) ≃
      Σ ( ternary-coproduct-Decomposition-subuniverse P X)
        ( λ d →
          inclusion-subuniverse ( subuniverse-global-subuniverse Q l2)
            ( S (first-summand-ternary-coproduct-Decomposition-subuniverse P X d)) ×
            ( inclusion-subuniverse ( subuniverse-global-subuniverse Q l3)
              ( T (second-summand-ternary-coproduct-Decomposition-subuniverse P X d)) ×
                inclusion-subuniverse ( subuniverse-global-subuniverse Q l4)
              ( U (third-summand-ternary-coproduct-Decomposition-subuniverse P X d))))
    equiv-right-iterated-cauchy-product-species-subuniverse =
      ( ( equiv-Σ-equiv-base
          ( _)
          ( equiv-ternary-right-iterated-coproduct-Decomposition-subuniverse P X C2)) ∘e
        ( ( inv-assoc-Σ
            ( binary-coproduct-Decomposition-subuniverse P X)
            ( λ z → binary-coproduct-Decomposition-subuniverse P (pr1 (pr2 z)))
            ( _)) ∘e
          ( ( equiv-tot (λ d → left-distributive-prod-Σ)))))

    equiv-associative-cauchy-product-species-subuniverse :
      cauchy-product-species-subuniverse' P Q
        ( cauchy-product-species-subuniverse P Q C1 S T)
        ( U)
        ( X) ≃
      cauchy-product-species-subuniverse' P Q
        ( S)
        ( cauchy-product-species-subuniverse P Q C1 T U)
        ( X)
    equiv-associative-cauchy-product-species-subuniverse =
      inv-equiv (equiv-right-iterated-cauchy-product-species-subuniverse) ∘e
      equiv-left-iterated-cauchy-product-species-subuniverse

  module _
    (S : species-subuniverse P ( subuniverse-global-subuniverse Q l2))
    (T : species-subuniverse P ( subuniverse-global-subuniverse Q l3))
    (U : species-subuniverse P ( subuniverse-global-subuniverse Q l4))
    where

    associative-cauchy-product-species-subuniverse :
      cauchy-product-species-subuniverse P Q C1
        ( cauchy-product-species-subuniverse P Q C1 S T)
        ( U) ＝
      cauchy-product-species-subuniverse P Q C1
        ( S)
        ( cauchy-product-species-subuniverse P Q C1 T U)
    associative-cauchy-product-species-subuniverse =
      eq-equiv-fam-subuniverse
        ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
        ( cauchy-product-species-subuniverse P Q C1
          ( cauchy-product-species-subuniverse P Q C1 S T)
          ( U))
        ( cauchy-product-species-subuniverse P Q C1
          ( S)
          ( cauchy-product-species-subuniverse P Q C1 T U))
        ( equiv-associative-cauchy-product-species-subuniverse S T U)
```

### Cauchy product is commutative

```agda
module _
  {l1 l2 l3 : Level}
  (P : subuniverse l1 l1)
  (Q : global-subuniverse id)
  ( C1 :
    ( (l4 l5 : Level)
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l4))
    (T : species-subuniverse P (subuniverse-global-subuniverse Q l5))
    (X : type-subuniverse P) →
      is-in-subuniverse
        ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l4 ⊔ l5))
        ( cauchy-product-species-subuniverse' P Q S T X)))
  (S : species-subuniverse P ( subuniverse-global-subuniverse Q l2))
  (T : species-subuniverse P ( subuniverse-global-subuniverse Q l3))
  where

  equiv-commutative-cauchy-product-species-subuniverse :
    (X : type-subuniverse P) →
    cauchy-product-species-subuniverse' P Q S T X ≃
    cauchy-product-species-subuniverse' P Q T S X
  equiv-commutative-cauchy-product-species-subuniverse X =
    equiv-Σ
      ( λ d →
        inclusion-subuniverse ( subuniverse-global-subuniverse Q l3)
          ( T (left-summand-binary-coproduct-Decomposition-subuniverse P X d)) ×
        inclusion-subuniverse ( subuniverse-global-subuniverse Q l2)
          ( S (right-summand-binary-coproduct-Decomposition-subuniverse P X d)))
      ( equiv-commutative-binary-coproduct-Decomposition-subuniverse P X)
      ( λ _ → commutative-prod)

  commutative-cauchy-product-species-subuniverse :
    cauchy-product-species-subuniverse P Q C1 S T ＝
    cauchy-product-species-subuniverse P Q C1 T S
  commutative-cauchy-product-species-subuniverse =
    eq-equiv-fam-subuniverse
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
      ( cauchy-product-species-subuniverse P Q C1 S T)
      ( cauchy-product-species-subuniverse P Q C1 T S)
      ( equiv-commutative-cauchy-product-species-subuniverse)
```

### Unit laws of Cauchy product

```agda
unit-cauchy-product-species-subuniverse :
  {l1 : Level} → (P : subuniverse l1 l1) → (Q : subuniverse l1 l1) →
  ( (X : type-subuniverse P) →
    is-in-subuniverse Q ( is-empty (inclusion-subuniverse P X))) →
  species-subuniverse P Q
unit-cauchy-product-species-subuniverse P Q C X =
  is-empty (inclusion-subuniverse P X) , C X

module _
  {l1 l2 : Level} (P : subuniverse l1 l1) (Q : global-subuniverse id)
  (C1 :
    ( (l4 l5 : Level)
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l4))
    (T : species-subuniverse P (subuniverse-global-subuniverse Q l5))
    (X : type-subuniverse P) →
      is-in-subuniverse
        ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l4 ⊔ l5))
        ( cauchy-product-species-subuniverse' P Q S T X)))
  (C2 : is-in-subuniverse P (raise-empty l1))
  (C3 :
    (X : type-subuniverse P) →
    is-in-subuniverse
      ( subuniverse-global-subuniverse Q l1)
      ( is-empty (inclusion-subuniverse P X)))
  (S : species-subuniverse P ( subuniverse-global-subuniverse Q l2))
  where

  equiv-right-unit-law-cauchy-product-species-subuniverse :
    {l : Level} →
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l)) →
    (X : type-subuniverse P) →
    cauchy-product-species-subuniverse' P Q
      ( S)
      ( unit-cauchy-product-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l1)
        ( C3))
      ( X) ≃
    inclusion-subuniverse (subuniverse-global-subuniverse Q l) (S X)
  equiv-right-unit-law-cauchy-product-species-subuniverse {l} S X =
    ( ( left-unit-law-Σ-is-contr
        ( is-contr-total-equiv-subuniverse P X)
        ( X , id-equiv)) ∘e
      ( ( equiv-Σ-equiv-base
          ( λ p →
            inclusion-subuniverse
              ( subuniverse-global-subuniverse Q l)
              ( S (pr1 (p))))
          ( equiv-is-empty-right-summand-binary-coproduct-Decomposition-subuniverse
            P
            X
            C2)) ∘e
        ( ( inv-assoc-Σ
            ( binary-coproduct-Decomposition-subuniverse P X)
            ( λ d →
              inclusion-subuniverse
                ( subuniverse-global-subuniverse Q l1)
                ( unit-cauchy-product-species-subuniverse
                  ( P)
                  ( subuniverse-global-subuniverse Q l1)
                  ( C3)
                  ( right-summand-binary-coproduct-Decomposition-subuniverse P X d)))
            ( λ z →
              inclusion-subuniverse
                ( subuniverse-global-subuniverse Q l)
                ( S
                  ( left-summand-binary-coproduct-Decomposition-subuniverse
                    P
                    X
                    (pr1 z))))) ∘e
          ( ( equiv-tot (λ _ → commutative-prod))))))

  equiv-left-unit-law-cauchy-product-species-subuniverse :
    {l : Level} →
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l)) →
    (X : type-subuniverse P) →
    cauchy-product-species-subuniverse' P Q
      ( unit-cauchy-product-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l1)
        ( C3))
      ( S)
      ( X) ≃
    inclusion-subuniverse (subuniverse-global-subuniverse Q l) (S X)
  equiv-left-unit-law-cauchy-product-species-subuniverse {l} S X =
    equiv-right-unit-law-cauchy-product-species-subuniverse S X ∘e
    equiv-commutative-cauchy-product-species-subuniverse
      ( P)
      ( Q)
      ( C1)
      ( unit-cauchy-product-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l1)
        ( C3))
      ( S)
      ( X)
```

### Equivalent form with species of types

```agda
module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l1) (Q : global-subuniverse id )
  ( C1 :
    ( (l4 l5 : Level)
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l4))
    (T : species-subuniverse P (subuniverse-global-subuniverse Q l5))
    (X : type-subuniverse P) →
      is-in-subuniverse
        ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l4 ⊔ l5))
        ( cauchy-product-species-subuniverse' P Q S T X)))
  ( C2 :
    ( A B : UU l1) →
    is-in-subuniverse P A →
    is-in-subuniverse P B →
    is-in-subuniverse P (A + B))
  (S : species-subuniverse P (subuniverse-global-subuniverse Q l2))
  (T : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  (X : UU l1)
  where

  private
    reassociate :
      Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
        ( cauchy-product-species-subuniverse P Q C1 S T)
        ( X) ≃
      Σ ( binary-coproduct-Decomposition l1 l1 X )
        ( λ (A , B , e) →
          Σ ( ( is-in-subuniverse P A × is-in-subuniverse P B) ×
              is-in-subuniverse P X)
            ( λ ((pA , pB) , pX) →
              inclusion-subuniverse
                ( subuniverse-global-subuniverse Q l2)
                ( S (A , pA)) ×
              inclusion-subuniverse
                ( subuniverse-global-subuniverse Q l3)
                ( T (B , pB)) ))
    pr1 reassociate (pX , ((A , pA) , (B , pB) , e) , s , t) =
      (A , B , e) , ((pA , pB) , pX) , (s , t)
    pr2 reassociate = is-equiv-has-inverse
      ( λ ((A , B , e) , ((pA , pB) , pX) , (s , t)) →
        ( pX , ((A , pA) , (B , pB) , e) , s , t))
      ( refl-htpy)
      ( refl-htpy)

    reassociate' :
      Σ ( binary-coproduct-Decomposition l1 l1 X )
        ( λ d →
           Σ ( Σ (pr1 (P (pr1 d))) (λ v → pr1 (P (pr1 (pr2 d)))))
           (λ p → pr1 (S (pr1 d , pr1 p)) × pr1 (T (pr1 (pr2 d) , pr2 p))))
      ≃
      cauchy-product-species-types
      (Σ-extension-species-subuniverse P
       (subuniverse-global-subuniverse Q l2) S)
      (Σ-extension-species-subuniverse P
       (subuniverse-global-subuniverse Q l3) T)
      X
    pr1 reassociate' (d , (pA , pB) , s , t) =
      d , (pA , s) , (pB , t)
    pr2 reassociate' =
      is-equiv-has-inverse
        ( λ ( d , (pA , s) , (pB , t)) → (d , (pA , pB) , s , t))
        ( refl-htpy)
        ( refl-htpy)

  equiv-cauchy-product-Σ-extension-species-subuniverse :
    Σ-extension-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3))
      ( cauchy-product-species-subuniverse P Q C1 S T)
      ( X) ≃
    cauchy-product-species-types
      ( Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l2)
        ( S))
      ( Σ-extension-species-subuniverse
        ( P)
        ( subuniverse-global-subuniverse Q l3)
        ( T))
      ( X)
  equiv-cauchy-product-Σ-extension-species-subuniverse =
    ( ( reassociate') ∘e
      ( ( equiv-tot
            ( λ d →
              equiv-Σ-equiv-base
                (λ p →
                    ( inclusion-subuniverse
                        ( subuniverse-global-subuniverse Q l2)
                        ( S ( left-summand-binary-coproduct-Decomposition d ,
                              pr1 p))) ×
                    ( inclusion-subuniverse
                        ( subuniverse-global-subuniverse Q l3)
                        ( T ( right-summand-binary-coproduct-Decomposition d ,
                              pr2 p))))
                ( inv-equiv
                    ( equiv-add-redundant-prop
                      ( is-prop-type-Prop (P X))
                      ( λ p →
                        tr
                          ( is-in-subuniverse P)
                          ( inv
                            ( eq-equiv
                                ( X)
                                ( left-summand-binary-coproduct-Decomposition d +
                                  right-summand-binary-coproduct-Decomposition d)
                                ( matching-correspondence-binary-coproduct-Decomposition d)))
                          ( C2
                            ( left-summand-binary-coproduct-Decomposition d)
                            ( right-summand-binary-coproduct-Decomposition d)
                            ( pr1 p)
                            ( pr2 p))))))) ∘e
        ( ( reassociate))))
```
