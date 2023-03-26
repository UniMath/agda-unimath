# Coproduct decompositions

```agda
module foundation.coproduct-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.propositions
open import foundation.subuniverses
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.univalence
open import foundation.universe-levels
```

</details>

## Definitions

### Binary coproduct decomposition

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  binary-coproduct-Decomposition : UU (lsuc l1 ⊔ l2)
  binary-coproduct-Decomposition =
    Σ ( type-subuniverse P)
        ( λ k1 →
          Σ ( type-subuniverse P)
            ( λ k2 →
              ( inclusion-subuniverse P X ≃
                ( (inclusion-subuniverse P k1) +
                  (inclusion-subuniverse P k2)))))

module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  (d : binary-coproduct-Decomposition P X)
  where

  left-summand-binary-coproduct-Decomposition : type-subuniverse P
  left-summand-binary-coproduct-Decomposition = pr1 d

  type-left-summand-binary-coproduct-Decomposition : UU l1
  type-left-summand-binary-coproduct-Decomposition =
    inclusion-subuniverse P left-summand-binary-coproduct-Decomposition

  right-summand-binary-coproduct-Decomposition : type-subuniverse P
  right-summand-binary-coproduct-Decomposition = pr1 (pr2 d)

  type-right-summand-binary-coproduct-Decomposition : UU l1
  type-right-summand-binary-coproduct-Decomposition =
    inclusion-subuniverse P right-summand-binary-coproduct-Decomposition

  matching-correspondence-coproductuct-decomposition :
    inclusion-subuniverse P X ≃
    ( type-left-summand-binary-coproduct-Decomposition +
      type-right-summand-binary-coproduct-Decomposition)
  matching-correspondence-coproductuct-decomposition = pr2 (pr2 d)
```

### Iterated binary coproduct decompositions

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  left-iterated-binary-coproduct-Decomposition : UU (lsuc l1 ⊔ l2)
  left-iterated-binary-coproduct-Decomposition =
    Σ ( binary-coproduct-Decomposition P X)
      ( λ d →
        binary-coproduct-Decomposition
          ( P)
          ( left-summand-binary-coproduct-Decomposition P X d))

  right-iterated-binary-coproduct-Decomposition : UU (lsuc l1 ⊔ l2)
  right-iterated-binary-coproduct-Decomposition =
    Σ ( binary-coproduct-Decomposition P X)
       ( λ d →
         binary-coproduct-Decomposition
           ( P)
           ( right-summand-binary-coproduct-Decomposition P X d))
```

### Ternary coproduct Decompositions

```agda
module _
  {l1 l2} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  ternary-coproduct-Decomposition : UU (lsuc l1 ⊔ l2)
  ternary-coproduct-Decomposition =
    Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
       ( λ x →
         inclusion-subuniverse P X ≃
         ( inclusion-subuniverse P (pr1 x) +
           ( inclusion-subuniverse P (pr1 (pr2 x)) +
             inclusion-subuniverse P (pr2 (pr2 x)))))

  module _
    (d : ternary-coproduct-Decomposition )
    where

    types-ternary-coproduct-Decomposition :
      type-subuniverse P × (type-subuniverse P × type-subuniverse P)
    types-ternary-coproduct-Decomposition = pr1 d

    first-summand-ternary-coproduct-Decomposition : type-subuniverse P
    first-summand-ternary-coproduct-Decomposition =
      (pr1 types-ternary-coproduct-Decomposition)

    second-summand-ternary-coproduct-Decomposition : type-subuniverse P
    second-summand-ternary-coproduct-Decomposition =
      (pr1 (pr2 types-ternary-coproduct-Decomposition))

    third-summand-ternary-coproduct-Decomposition : type-subuniverse P
    third-summand-ternary-coproduct-Decomposition =
      (pr2 (pr2 types-ternary-coproduct-Decomposition))

    matching-correspondence-ternary-coproductuct-Decomposition :
      inclusion-subuniverse P X ≃
      ( inclusion-subuniverse P first-summand-ternary-coproduct-Decomposition +
        ( inclusion-subuniverse
            P
            second-summand-ternary-coproduct-Decomposition +
          inclusion-subuniverse P third-summand-ternary-coproduct-Decomposition))
    matching-correspondence-ternary-coproductuct-Decomposition = pr2 d
```

## Propositions

### Equivalence between binary coproduct Decomposition induce by commutativiy of coproduct

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  equiv-commutative-binary-coproduct-Decomposition :
    binary-coproduct-Decomposition P X ≃ binary-coproduct-Decomposition P X
  equiv-commutative-binary-coproduct-Decomposition =
    ( ( assoc-Σ
        ( type-subuniverse P)
        ( λ _ → type-subuniverse P)
        ( _)) ∘e
      ( ( equiv-Σ
          ( _)
          ( commutative-prod)
          ( λ x →
            equiv-postcomp-equiv
              ( commutative-coprod
                ( inclusion-subuniverse P (pr1 x))
                ( inclusion-subuniverse P (pr2 x)))
              (inclusion-subuniverse P X))) ∘e
        ( ( inv-assoc-Σ
            ( type-subuniverse P)
            ( λ _ → type-subuniverse P)
            ( _)))))
```

### Equivalence between iterated coproduct and ternary coproduct decomposition

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  (C1 :
    (A : type-subuniverse P) → (B : type-subuniverse P) →
    is-in-subuniverse P (inclusion-subuniverse P A + inclusion-subuniverse P B))
  where

  private
    map-reassociate-left-iterated-coproduct-Decomposition :
      left-iterated-binary-coproduct-Decomposition P X →
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ A →
                  inclusion-subuniverse P A ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) +
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ A →
              inclusion-subuniverse P X ≃
              ( inclusion-subuniverse P (pr1 A) +
                inclusion-subuniverse P (pr1 x))))
    map-reassociate-left-iterated-coproduct-Decomposition ((A , B , e) , C , D , f) =
      ( (B , C , D) , (A , f) , e )

    map-inv-reassociate-left-iterated-coproduct-Decomposition :
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ A →
                  inclusion-subuniverse P A ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) +
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ A →
              inclusion-subuniverse P X ≃
              ( inclusion-subuniverse P (pr1 A) +
                inclusion-subuniverse P (pr1 x)))) →
      left-iterated-binary-coproduct-Decomposition P X
    map-inv-reassociate-left-iterated-coproduct-Decomposition ( (B , C , D) , (A , f) , e ) =
      ((A , B , e) , C , D , f)

    equiv-reassociate-left-iterated-coproduct-Decomposition :
      left-iterated-binary-coproduct-Decomposition P X ≃
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ A →
                  inclusion-subuniverse P A ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) +
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ A →
              inclusion-subuniverse P X ≃
              ( inclusion-subuniverse P (pr1 A) +
                inclusion-subuniverse P (pr1 x))))
    pr1 equiv-reassociate-left-iterated-coproduct-Decomposition =
      map-reassociate-left-iterated-coproduct-Decomposition
    pr2 equiv-reassociate-left-iterated-coproduct-Decomposition =
      is-equiv-has-inverse
        map-inv-reassociate-left-iterated-coproduct-Decomposition
        refl-htpy
        refl-htpy

  equiv-ternary-left-iterated-coproduct-Decomposition :
    left-iterated-binary-coproduct-Decomposition P X ≃
    ternary-coproduct-Decomposition P X
  equiv-ternary-left-iterated-coproduct-Decomposition =
    ( ( equiv-tot
        ( λ x →
          ( ( equiv-postcomp-equiv
              ( commutative-coprod _ _)
              ( inclusion-subuniverse P X)) ∘e
          ( ( left-unit-law-Σ-is-contr
              ( is-contr-total-equiv-subuniverse'
                ( P)
                ( ( inclusion-subuniverse P (pr1 (pr2 x)) +
                    inclusion-subuniverse P (pr2 (pr2 x))) ,
                  C1 (pr1 (pr2 x)) (pr2 (pr2 x)))))
              ( ( ( inclusion-subuniverse P (pr1 (pr2 x)) +
                    inclusion-subuniverse P (pr2 (pr2 x))) ,
                  C1 (pr1 (pr2 x)) (pr2 (pr2 x))) ,
                id-equiv))))) ∘e
      ( ( equiv-reassociate-left-iterated-coproduct-Decomposition)))

  private
    map-reassociate-right-iterated-coproduct-Decomposition :
      right-iterated-binary-coproduct-Decomposition P X →
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ B →
                  inclusion-subuniverse P B ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) +
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ B →
              inclusion-subuniverse P X ≃
              ( inclusion-subuniverse P (pr1 x) +
                inclusion-subuniverse P (pr1 B))))
    map-reassociate-right-iterated-coproduct-Decomposition ((A , B , e) , C , D , f) =
      ( (A , C , D) , (B , f) , e )

    map-inv-reassociate-right-iterated-coproduct-Decomposition :
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ B →
                  inclusion-subuniverse P B ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) +
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ B →
              inclusion-subuniverse P X ≃
              ( inclusion-subuniverse P (pr1 x) +
                inclusion-subuniverse P (pr1 B)))) →
      right-iterated-binary-coproduct-Decomposition P X
    map-inv-reassociate-right-iterated-coproduct-Decomposition ( (A , C , D) , (B , f) , e ) =
      ((A , B , e) , C , D , f)

    equiv-reassociate-right-iterated-coproduct-Decomposition :
      right-iterated-binary-coproduct-Decomposition P X ≃
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ B →
                  inclusion-subuniverse P B ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) +
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ B →
              inclusion-subuniverse P X ≃
              ( inclusion-subuniverse P (pr1 x) +
                inclusion-subuniverse P (pr1 B))))
    pr1 equiv-reassociate-right-iterated-coproduct-Decomposition =
      map-reassociate-right-iterated-coproduct-Decomposition
    pr2 equiv-reassociate-right-iterated-coproduct-Decomposition =
      is-equiv-has-inverse
        map-inv-reassociate-right-iterated-coproduct-Decomposition
        refl-htpy
        refl-htpy

  equiv-ternary-right-iterated-coproduct-Decomposition :
    right-iterated-binary-coproduct-Decomposition P X ≃
    ternary-coproduct-Decomposition P X
  equiv-ternary-right-iterated-coproduct-Decomposition =
    ( ( equiv-tot
        ( λ x →
          left-unit-law-Σ-is-contr
            ( is-contr-total-equiv-subuniverse'
              ( P)
              ( ( inclusion-subuniverse P (pr1 (pr2 x)) +
                  inclusion-subuniverse P (pr2 (pr2 x))) ,
                ( C1 (pr1 (pr2 x)) (pr2 (pr2 x)))))
            ( ( ( inclusion-subuniverse P (pr1 (pr2 x)) +
                  inclusion-subuniverse P (pr2 (pr2 x))) ,
                ( C1 (pr1 (pr2 x)) (pr2 (pr2 x)))) ,
              id-equiv))) ∘e
      ( ( equiv-reassociate-right-iterated-coproduct-Decomposition)))
```

### Coproduct-decomposition with empty right summand

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  (C1 : is-in-subuniverse P (raise-empty l1))
  where

  equiv-is-empty-right-summand-binary-coproduct-Decomposition :
    ( Σ ( binary-coproduct-Decomposition P X)
        ( λ d →
          is-empty
            ( inclusion-subuniverse P
              ( right-summand-binary-coproduct-Decomposition P X d)))) ≃
    Σ ( type-subuniverse P)
      ( λ Y → inclusion-subuniverse P X ≃ pr1 Y)
  equiv-is-empty-right-summand-binary-coproduct-Decomposition =
    ( ( equiv-tot
          ( λ x →
            ( ( equiv-postcomp-equiv
                ( right-unit-law-coprod-is-empty
                  ( inclusion-subuniverse P x)
                  ( raise-empty l1)
                  ( is-empty-raise-empty))
                ( inclusion-subuniverse P X)) ∘e
              ( ( left-unit-law-Σ-is-contr
                     ( ( ( ( raise-empty l1) ,
                           C1) ,
                         is-empty-raise-empty) ,
                       ( λ x →
                         eq-pair-Σ
                           ( eq-pair-Σ
                             ( eq-equiv
                               ( raise-empty l1)
                               ( inclusion-subuniverse P (pr1 x))
                               ( equiv-is-empty
                                 is-empty-raise-empty
                                 ( ( pr2 x))))
                             ( eq-is-prop (is-prop-type-Prop (P _))))
                           ( eq-is-prop is-prop-is-empty)))
                     ( ( raise-empty l1 , C1) ,
                       is-empty-raise-empty)) ∘e
                ( ( inv-assoc-Σ _ _ _) ∘e
                  ( ( equiv-tot (λ _ → commutative-prod)) ∘e
                    ( ( assoc-Σ _ _ _)))))))) ∘e
        ( ( assoc-Σ _ _ _)))
```
