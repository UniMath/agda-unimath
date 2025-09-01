# Product decompositions of types in a subuniverse

```agda
module foundation.product-decompositions-subuniverse where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.subuniverses
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.propositions
```

</details>

## Definitions

### Binary product decomposition of types in a subuniverse

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  binary-product-Decomposition-Subuniverse : UU (lsuc l1 ⊔ l2)
  binary-product-Decomposition-Subuniverse =
    Σ ( type-subuniverse P)
        ( λ k1 →
          Σ ( type-subuniverse P)
            ( λ k2 →
              ( inclusion-subuniverse P X ≃
                ( (inclusion-subuniverse P k1) ×
                  (inclusion-subuniverse P k2)))))

module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  (d : binary-product-Decomposition-Subuniverse P X)
  where

  left-summand-binary-product-Decomposition-Subuniverse : type-subuniverse P
  left-summand-binary-product-Decomposition-Subuniverse = pr1 d

  type-left-summand-binary-product-Decomposition-Subuniverse : UU l1
  type-left-summand-binary-product-Decomposition-Subuniverse =
    inclusion-subuniverse
      P
      left-summand-binary-product-Decomposition-Subuniverse

  right-summand-binary-product-Decomposition-Subuniverse : type-subuniverse P
  right-summand-binary-product-Decomposition-Subuniverse = pr1 (pr2 d)

  type-right-summand-binary-product-Decomposition-Subuniverse : UU l1
  type-right-summand-binary-product-Decomposition-Subuniverse =
    inclusion-subuniverse
      P
      right-summand-binary-product-Decomposition-Subuniverse

  matching-correspondence-binary-product-Decomposition-Subuniverse :
    inclusion-subuniverse P X ≃
    ( type-left-summand-binary-product-Decomposition-Subuniverse ×
      type-right-summand-binary-product-Decomposition-Subuniverse)
  matching-correspondence-binary-product-Decomposition-Subuniverse = pr2 (pr2 d)
```

### Iterated binary product decompositions

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  left-iterated-binary-product-Decomposition-Subuniverse : UU (lsuc l1 ⊔ l2)
  left-iterated-binary-product-Decomposition-Subuniverse =
    Σ ( binary-product-Decomposition-Subuniverse P X)
      ( λ d →
        binary-product-Decomposition-Subuniverse
          ( P)
          ( left-summand-binary-product-Decomposition-Subuniverse P X d))

  right-iterated-binary-product-Decomposition-Subuniverse : UU (lsuc l1 ⊔ l2)
  right-iterated-binary-product-Decomposition-Subuniverse =
    Σ ( binary-product-Decomposition-Subuniverse P X)
      ( λ d →
        binary-product-Decomposition-Subuniverse
          ( P)
          ( right-summand-binary-product-Decomposition-Subuniverse P X d))
```

### Ternary product Decomposition-subuniverses

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  ternary-product-Decomposition-Subuniverse : UU (lsuc l1 ⊔ l2)
  ternary-product-Decomposition-Subuniverse =
    Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
      ( λ x →
        inclusion-subuniverse P X ≃
        ( inclusion-subuniverse P (pr1 x) ×
          ( inclusion-subuniverse P (pr1 (pr2 x)) ×
            inclusion-subuniverse P (pr2 (pr2 x)))))

  module _
    (d : ternary-product-Decomposition-Subuniverse)
    where

    types-ternary-product-Decomposition-Subuniverse :
      type-subuniverse P × (type-subuniverse P × type-subuniverse P)
    types-ternary-product-Decomposition-Subuniverse = pr1 d

    first-summand-ternary-product-Decomposition-Subuniverse : type-subuniverse P
    first-summand-ternary-product-Decomposition-Subuniverse =
      (pr1 types-ternary-product-Decomposition-Subuniverse)

    second-summand-ternary-product-Decomposition-Subuniverse :
      type-subuniverse P
    second-summand-ternary-product-Decomposition-Subuniverse =
      (pr1 (pr2 types-ternary-product-Decomposition-Subuniverse))

    third-summand-ternary-product-Decomposition-Subuniverse : type-subuniverse P
    third-summand-ternary-product-Decomposition-Subuniverse =
      (pr2 (pr2 types-ternary-product-Decomposition-Subuniverse))

    matching-correspondence-ternary-productuct-Decomposition-Subuniverse :
      inclusion-subuniverse P X ≃
      ( inclusion-subuniverse
        P
        first-summand-ternary-product-Decomposition-Subuniverse ×
        ( ( inclusion-subuniverse
            P
            second-summand-ternary-product-Decomposition-Subuniverse) ×
          inclusion-subuniverse
            P
            third-summand-ternary-product-Decomposition-Subuniverse))
    matching-correspondence-ternary-productuct-Decomposition-Subuniverse = pr2 d
```

## Propositions

### Equivalence between binary product Decomposition-Subuniverse induce by

commutativiy of product

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  equiv-commutative-binary-product-Decomposition-Subuniverse :
    binary-product-Decomposition-Subuniverse P X ≃
    binary-product-Decomposition-Subuniverse P X
  equiv-commutative-binary-product-Decomposition-Subuniverse =
    ( associative-Σ) ∘e
    ( ( equiv-Σ
        ( _)
        ( commutative-product)
        ( λ x →
          equiv-postcomp-equiv
            ( commutative-product)
            ( inclusion-subuniverse P X))) ∘e
      ( inv-associative-Σ))
```

### Equivalence between iterated product and ternary product decomposition

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  (C1 : is-closed-under-products-subuniverse P)
  where

  private
    map-reassociate-left-iterated-product-Decomposition-Subuniverse :
      left-iterated-binary-product-Decomposition-Subuniverse P X →
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
    map-reassociate-left-iterated-product-Decomposition-Subuniverse
      ( (A , B , e) , C , D , f) =
      ( (B , C , D) , (A , f) , e)

    map-inv-reassociate-left-iterated-product-Decomposition-Subuniverse :
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
      left-iterated-binary-product-Decomposition-Subuniverse P X
    map-inv-reassociate-left-iterated-product-Decomposition-Subuniverse
      ( (B , C , D) , (A , f) , e) =
      ( (A , B , e) , C , D , f)

    equiv-reassociate-left-iterated-product-Decomposition-Subuniverse :
      left-iterated-binary-product-Decomposition-Subuniverse P X ≃
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
    pr1 equiv-reassociate-left-iterated-product-Decomposition-Subuniverse =
      map-reassociate-left-iterated-product-Decomposition-Subuniverse
    pr2 equiv-reassociate-left-iterated-product-Decomposition-Subuniverse =
      is-equiv-is-invertible
        map-inv-reassociate-left-iterated-product-Decomposition-Subuniverse
        refl-htpy
        refl-htpy

  equiv-ternary-left-iterated-product-Decomposition-Subuniverse :
    left-iterated-binary-product-Decomposition-Subuniverse P X ≃
    ternary-product-Decomposition-Subuniverse P X
  equiv-ternary-left-iterated-product-Decomposition-Subuniverse =
    ( ( equiv-tot
        ( λ x →
          ( ( equiv-postcomp-equiv
              ( commutative-product)
              ( inclusion-subuniverse P X)) ∘e
            ( ( left-unit-law-Σ-is-contr
                ( is-torsorial-equiv-subuniverse'
                  ( P)
                  ( ( inclusion-subuniverse P (pr1 (pr2 x)) ×
                      inclusion-subuniverse P (pr2 (pr2 x))) ,
                    C1 (pr2 (pr1 (pr2 x))) (pr2 (pr2 (pr2 x))))))
                ( ( ( inclusion-subuniverse P (pr1 (pr2 x)) ×
                      inclusion-subuniverse P (pr2 (pr2 x))) ,
                    C1 (pr2 (pr1 (pr2 x))) (pr2 (pr2 (pr2 x)))) ,
                  id-equiv))))) ∘e
      ( ( equiv-reassociate-left-iterated-product-Decomposition-Subuniverse)))

  private
    map-reassociate-right-iterated-product-Decomposition-Subuniverse :
      right-iterated-binary-product-Decomposition-Subuniverse P X →
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
    map-reassociate-right-iterated-product-Decomposition-Subuniverse
      ( (A , B , e) , C , D , f) =
      ( (A , C , D) , (B , f) , e)

    map-inv-reassociate-right-iterated-product-Decomposition-Subuniverse :
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
      right-iterated-binary-product-Decomposition-Subuniverse P X
    map-inv-reassociate-right-iterated-product-Decomposition-Subuniverse
      ( (A , C , D) , (B , f) , e) =
      ( (A , B , e) , C , D , f)

    equiv-reassociate-right-iterated-product-Decomposition-Subuniverse :
      right-iterated-binary-product-Decomposition-Subuniverse P X ≃
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
    pr1 equiv-reassociate-right-iterated-product-Decomposition-Subuniverse =
      map-reassociate-right-iterated-product-Decomposition-Subuniverse
    pr2 equiv-reassociate-right-iterated-product-Decomposition-Subuniverse =
      is-equiv-is-invertible
        map-inv-reassociate-right-iterated-product-Decomposition-Subuniverse
        refl-htpy
        refl-htpy

  equiv-ternary-right-iterated-product-Decomposition-Subuniverse :
    right-iterated-binary-product-Decomposition-Subuniverse P X ≃
    ternary-product-Decomposition-Subuniverse P X
  equiv-ternary-right-iterated-product-Decomposition-Subuniverse =
    ( ( equiv-tot
        ( λ x →
          left-unit-law-Σ-is-contr
            ( is-torsorial-equiv-subuniverse'
              ( P)
              ( ( inclusion-subuniverse P (pr1 (pr2 x)) ×
                  inclusion-subuniverse P (pr2 (pr2 x))) ,
                ( C1 (pr2 (pr1 (pr2 x))) (pr2 (pr2 (pr2 x))))))
            ( ( ( inclusion-subuniverse P (pr1 (pr2 x)) ×
                  inclusion-subuniverse P (pr2 (pr2 x))) ,
                ( C1 (pr2 (pr1 (pr2 x))) (pr2 (pr2 (pr2 x))))) ,
              id-equiv))) ∘e
      ( ( equiv-reassociate-right-iterated-product-Decomposition-Subuniverse)))
```

### Product-decomposition with contractible right summand

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  (C1 : is-in-subuniverse P (raise-unit l1))
  where

  equiv-is-contr-right-summand-binary-product-Decomposition-Subuniverse :
    ( Σ ( binary-product-Decomposition-Subuniverse P X)
        ( λ d →
          is-contr
            ( inclusion-subuniverse P
              ( right-summand-binary-product-Decomposition-Subuniverse
                P
                X
                d)))) ≃
    Σ ( type-subuniverse P)
      ( λ Y → inclusion-subuniverse P X ≃ pr1 Y)
  equiv-is-contr-right-summand-binary-product-Decomposition-Subuniverse =
    ( ( equiv-tot
          ( λ x →
            ( ( equiv-postcomp-equiv
                ( right-unit-law-product-is-contr is-contr-raise-unit)
                ( inclusion-subuniverse P X)) ∘e
              ( ( left-unit-law-Σ-is-contr
                  ( ( ( ( raise-unit l1) ,
                        C1) ,
                      is-contr-raise-unit) ,
                    ( λ x →
                      eq-pair-Σ
                        ( eq-pair-Σ
                          ( eq-equiv
                            ( equiv-is-contr is-contr-raise-unit (pr2 x)))
                          ( eq-is-prop (is-prop-type-Prop (P (pr1 (pr1 x))))))
                        ( eq-is-prop is-property-is-contr)))
                  ( ( raise-unit l1 , C1) ,
                    is-contr-raise-unit)) ∘e
                ( ( inv-associative-Σ) ∘e
                  ( ( equiv-tot (λ _ → commutative-product)) ∘e
                    ( ( associative-Σ)))))))) ∘e
        ( ( associative-Σ)))
```
