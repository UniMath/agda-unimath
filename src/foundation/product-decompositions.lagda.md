# Product decompositions

```agda
module foundation.product-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.propositions
open import foundation.subuniverses
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels
```

</details>

## Definitions

### Binary product decomposition

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  binary-product-Decomposition : UU (lsuc l1 ⊔ l2)
  binary-product-Decomposition =
    Σ ( type-subuniverse P)
        ( λ k1 →
          Σ ( type-subuniverse P)
            ( λ k2 →
              ( inclusion-subuniverse P X ≃
                ( (inclusion-subuniverse P k1) ×
                  (inclusion-subuniverse P k2)))))

module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  (d : binary-product-Decomposition P X)
  where

  left-summand-binary-product-Decomposition : type-subuniverse P
  left-summand-binary-product-Decomposition = pr1 d

  type-left-summand-binary-product-Decomposition : UU l1
  type-left-summand-binary-product-Decomposition =
    inclusion-subuniverse P left-summand-binary-product-Decomposition

  right-summand-binary-product-Decomposition : type-subuniverse P
  right-summand-binary-product-Decomposition = pr1 (pr2 d)

  type-right-summand-binary-product-Decomposition : UU l1
  type-right-summand-binary-product-Decomposition =
    inclusion-subuniverse P right-summand-binary-product-Decomposition

  matching-correspondence-productuct-decomposition :
    inclusion-subuniverse P X ≃
    ( type-left-summand-binary-product-Decomposition ×
      type-right-summand-binary-product-Decomposition)
  matching-correspondence-productuct-decomposition = pr2 (pr2 d)
```

### Iterated binary product decompositions

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  left-iterated-binary-product-Decomposition : UU (lsuc l1 ⊔ l2)
  left-iterated-binary-product-Decomposition =
    Σ ( binary-product-Decomposition P X)
      ( λ d →
        binary-product-Decomposition
          ( P)
          ( left-summand-binary-product-Decomposition P X d))

  right-iterated-binary-product-Decomposition : UU (lsuc l1 ⊔ l2)
  right-iterated-binary-product-Decomposition =
    Σ ( binary-product-Decomposition P X)
       ( λ d →
         binary-product-Decomposition
           ( P)
           ( right-summand-binary-product-Decomposition P X d))
```

### Ternary product Decompositions

```agda
module _
  {l1 l2} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  ternary-product-Decomposition : UU (lsuc l1 ⊔ l2)
  ternary-product-Decomposition =
    Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
       ( λ x →
         inclusion-subuniverse P X ≃
         ( inclusion-subuniverse P (pr1 x) ×
           ( inclusion-subuniverse P (pr1 (pr2 x)) ×
             inclusion-subuniverse P (pr2 (pr2 x)))))

  module _
    (d : ternary-product-Decomposition )
    where

    types-ternary-product-Decomposition :
      type-subuniverse P × (type-subuniverse P × type-subuniverse P)
    types-ternary-product-Decomposition = pr1 d

    first-summand-ternary-product-Decomposition : type-subuniverse P
    first-summand-ternary-product-Decomposition =
      (pr1 types-ternary-product-Decomposition)

    second-summand-ternary-product-Decomposition : type-subuniverse P
    second-summand-ternary-product-Decomposition =
      (pr1 (pr2 types-ternary-product-Decomposition))

    third-summand-ternary-product-Decomposition : type-subuniverse P
    third-summand-ternary-product-Decomposition =
      (pr2 (pr2 types-ternary-product-Decomposition))

    matching-correspondence-ternary-productuct-Decomposition :
      inclusion-subuniverse P X ≃
      ( inclusion-subuniverse P first-summand-ternary-product-Decomposition ×
        ( inclusion-subuniverse P second-summand-ternary-product-Decomposition ×
          inclusion-subuniverse P third-summand-ternary-product-Decomposition))
    matching-correspondence-ternary-productuct-Decomposition = pr2 d
```

## Propositions

### Equivalence between binary product Decomposition induce by commutativiy of product

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  equiv-commutative-binary-product-Decomposition :
    binary-product-Decomposition P X ≃ binary-product-Decomposition P X
  equiv-commutative-binary-product-Decomposition =
    ( ( assoc-Σ
        ( type-subuniverse P)
        ( λ _ → type-subuniverse P)
        ( _)) ∘e
      ( ( equiv-Σ
          ( _)
          ( commutative-prod)
          ( λ x →
            equiv-postcomp-equiv
              ( commutative-prod)
              (inclusion-subuniverse P X))) ∘e
        ( ( inv-assoc-Σ
            ( type-subuniverse P)
            ( λ _ → type-subuniverse P)
            ( _)))))
```

### Equivalence between iterated product and ternary product decomposition

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  (C1 :
    (A : type-subuniverse P) → (B : type-subuniverse P) →
    is-in-subuniverse P (inclusion-subuniverse P A × inclusion-subuniverse P B))
  where

  private
    map-reassociate-left-iterated-product-Decomposition :
      left-iterated-binary-product-Decomposition P X →
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ A →
                  inclusion-subuniverse P A ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) ×
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ A →
              inclusion-subuniverse P X ≃
              ( inclusion-subuniverse P (pr1 A) ×
                inclusion-subuniverse P (pr1 x))))
    map-reassociate-left-iterated-product-Decomposition ((A , B , e) , C , D , f) =
      ( (B , C , D) , (A , f) , e )

    map-inv-reassociate-left-iterated-product-Decomposition :
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ A →
                  inclusion-subuniverse P A ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) ×
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ A →
              inclusion-subuniverse P X ≃
              ( inclusion-subuniverse P (pr1 A) ×
                inclusion-subuniverse P (pr1 x)))) →
      left-iterated-binary-product-Decomposition P X
    map-inv-reassociate-left-iterated-product-Decomposition ( (B , C , D) , (A , f) , e ) =
      ((A , B , e) , C , D , f)

    equiv-reassociate-left-iterated-product-Decomposition :
      left-iterated-binary-product-Decomposition P X ≃
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ A →
                  inclusion-subuniverse P A ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) ×
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ A →
              inclusion-subuniverse P X ≃
              ( inclusion-subuniverse P (pr1 A) ×
                inclusion-subuniverse P (pr1 x))))
    pr1 equiv-reassociate-left-iterated-product-Decomposition =
      map-reassociate-left-iterated-product-Decomposition
    pr2 equiv-reassociate-left-iterated-product-Decomposition =
      is-equiv-has-inverse
        map-inv-reassociate-left-iterated-product-Decomposition
        refl-htpy
        refl-htpy

  equiv-ternary-left-iterated-product-Decomposition :
    left-iterated-binary-product-Decomposition P X ≃
    ternary-product-Decomposition P X
  equiv-ternary-left-iterated-product-Decomposition =
    ( ( equiv-tot
        ( λ x →
          ( ( equiv-postcomp-equiv
              ( commutative-prod)
              ( inclusion-subuniverse P X)) ∘e
            ( ( left-unit-law-Σ-is-contr
                ( is-contr-total-equiv-subuniverse'
                  ( P)
                  ( ( inclusion-subuniverse P (pr1 (pr2 x)) ×
                      inclusion-subuniverse P (pr2 (pr2 x))) ,
                    C1 (pr1 (pr2 x)) (pr2 (pr2 x)))))
                ( ( ( inclusion-subuniverse P (pr1 (pr2 x)) ×
                      inclusion-subuniverse P (pr2 (pr2 x))) ,
                    C1 (pr1 (pr2 x)) (pr2 (pr2 x))) ,
                  id-equiv))))) ∘e
      ( ( equiv-reassociate-left-iterated-product-Decomposition)))

  private
    map-reassociate-right-iterated-product-Decomposition :
      right-iterated-binary-product-Decomposition P X →
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ B →
                  inclusion-subuniverse P B ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) ×
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ B →
              inclusion-subuniverse P X ≃
              ( inclusion-subuniverse P (pr1 x) ×
                inclusion-subuniverse P (pr1 B))))
    map-reassociate-right-iterated-product-Decomposition ((A , B , e) , C , D , f) =
      ( (A , C , D) , (B , f) , e )

    map-inv-reassociate-right-iterated-product-Decomposition :
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ B →
                  inclusion-subuniverse P B ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) ×
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ B →
              inclusion-subuniverse P X ≃
              ( inclusion-subuniverse P (pr1 x) ×
                inclusion-subuniverse P (pr1 B)))) →
      right-iterated-binary-product-Decomposition P X
    map-inv-reassociate-right-iterated-product-Decomposition ( (A , C , D) , (B , f) , e ) =
      ((A , B , e) , C , D , f)

    equiv-reassociate-right-iterated-product-Decomposition :
      right-iterated-binary-product-Decomposition P X ≃
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ B →
                  inclusion-subuniverse P B ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) ×
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ B →
              inclusion-subuniverse P X ≃
              ( inclusion-subuniverse P (pr1 x) ×
                inclusion-subuniverse P (pr1 B))))
    pr1 equiv-reassociate-right-iterated-product-Decomposition =
      map-reassociate-right-iterated-product-Decomposition
    pr2 equiv-reassociate-right-iterated-product-Decomposition =
      is-equiv-has-inverse
        map-inv-reassociate-right-iterated-product-Decomposition
        refl-htpy
        refl-htpy

  equiv-ternary-right-iterated-product-Decomposition :
    right-iterated-binary-product-Decomposition P X ≃
    ternary-product-Decomposition P X
  equiv-ternary-right-iterated-product-Decomposition =
    ( ( equiv-tot
        ( λ x →
          left-unit-law-Σ-is-contr
            ( is-contr-total-equiv-subuniverse'
              ( P)
              ( ( inclusion-subuniverse P (pr1 (pr2 x)) ×
                  inclusion-subuniverse P (pr2 (pr2 x))) ,
                ( C1 (pr1 (pr2 x)) (pr2 (pr2 x)))))
            ( ( ( inclusion-subuniverse P (pr1 (pr2 x)) ×
                  inclusion-subuniverse P (pr2 (pr2 x))) ,
                ( C1 (pr1 (pr2 x)) (pr2 (pr2 x)))) ,
              id-equiv))) ∘e
      ( ( equiv-reassociate-right-iterated-product-Decomposition)))
```

### Product-decomposition with contractible right summand

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  (C1 : is-in-subuniverse P (raise-unit l1))
  where

  equiv-is-contr-right-summand-binary-product-Decomposition :
    ( Σ ( binary-product-Decomposition P X)
        ( λ d →
          is-contr
            ( inclusion-subuniverse P
              ( right-summand-binary-product-Decomposition P X d)))) ≃
    Σ ( type-subuniverse P)
      ( λ Y → inclusion-subuniverse P X ≃ pr1 Y)
  equiv-is-contr-right-summand-binary-product-Decomposition =
    ( ( equiv-tot
          ( λ x →
            ( ( equiv-postcomp-equiv
                ( right-unit-law-prod-is-contr is-contr-raise-unit)
                ( inclusion-subuniverse P X)) ∘e
              ( ( left-unit-law-Σ-is-contr
                     ( ( ( ( raise-unit l1) ,
                           C1) ,
                         is-contr-raise-unit) ,
                       ( λ x →
                         eq-pair-Σ
                           ( eq-pair-Σ
                             ( eq-equiv
                               ( raise-unit l1)
                               ( inclusion-subuniverse P (pr1 x))
                               ( equiv-is-contr
                                 is-contr-raise-unit
                                 ( ( pr2 x))))
                             ( eq-is-prop (is-prop-type-Prop (P _))))
                           ( eq-is-prop is-property-is-contr)))
                     ( ( raise-unit l1 , C1) ,
                       is-contr-raise-unit)) ∘e
                ( ( inv-assoc-Σ _ _ _) ∘e
                  ( ( equiv-tot (λ _ → commutative-prod)) ∘e
                    ( ( assoc-Σ _ _ _)))))))) ∘e
        ( ( assoc-Σ _ _ _)))
```
