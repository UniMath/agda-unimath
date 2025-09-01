# Coproduct decompositions in a subuniverse

```agda
module foundation.coproduct-decompositions-subuniverse where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.functoriality-coproduct-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.structure-identity-principle
open import foundation.subuniverses
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

Let `P` be a subuniverse and `X` a type in `P`. A binary coproduct decomposition
of `X` is defined to be two types `A` and `B` in `P` and an equivalence from `X`
to `A+B`.

## Definitions

### Binary coproduct decomposition

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  binary-coproduct-Decomposition-subuniverse : UU (lsuc l1 ⊔ l2)
  binary-coproduct-Decomposition-subuniverse =
    Σ ( type-subuniverse P)
      ( λ k1 →
        Σ ( type-subuniverse P)
          ( λ k2 →
            ( inclusion-subuniverse P X) ≃
            ( inclusion-subuniverse P k1 + inclusion-subuniverse P k2)))

module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  (d : binary-coproduct-Decomposition-subuniverse P X)
  where

  left-summand-binary-coproduct-Decomposition-subuniverse : type-subuniverse P
  left-summand-binary-coproduct-Decomposition-subuniverse = pr1 d

  type-left-summand-binary-coproduct-Decomposition-subuniverse : UU l1
  type-left-summand-binary-coproduct-Decomposition-subuniverse =
    inclusion-subuniverse P
      left-summand-binary-coproduct-Decomposition-subuniverse

  right-summand-binary-coproduct-Decomposition-subuniverse : type-subuniverse P
  right-summand-binary-coproduct-Decomposition-subuniverse = pr1 (pr2 d)

  type-right-summand-binary-coproduct-Decomposition-subuniverse : UU l1
  type-right-summand-binary-coproduct-Decomposition-subuniverse =
    inclusion-subuniverse P
      right-summand-binary-coproduct-Decomposition-subuniverse

  matching-correspondence-binary-coproduct-Decomposition-subuniverse :
    inclusion-subuniverse P X ≃
    ( type-left-summand-binary-coproduct-Decomposition-subuniverse +
      type-right-summand-binary-coproduct-Decomposition-subuniverse)
  matching-correspondence-binary-coproduct-Decomposition-subuniverse =
    pr2 (pr2 d)
```

### Iterated binary coproduct decompositions

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  left-iterated-binary-coproduct-Decomposition-subuniverse : UU (lsuc l1 ⊔ l2)
  left-iterated-binary-coproduct-Decomposition-subuniverse =
    Σ ( binary-coproduct-Decomposition-subuniverse P X)
      ( λ d →
        binary-coproduct-Decomposition-subuniverse P
          ( left-summand-binary-coproduct-Decomposition-subuniverse P X d))

  right-iterated-binary-coproduct-Decomposition-subuniverse : UU (lsuc l1 ⊔ l2)
  right-iterated-binary-coproduct-Decomposition-subuniverse =
    Σ ( binary-coproduct-Decomposition-subuniverse P X)
      ( λ d →
        binary-coproduct-Decomposition-subuniverse P
          ( right-summand-binary-coproduct-Decomposition-subuniverse P X d))
```

### Ternary coproduct Decomposition-subuniverses

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  ternary-coproduct-Decomposition-subuniverse : UU (lsuc l1 ⊔ l2)
  ternary-coproduct-Decomposition-subuniverse =
    Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
      ( λ x →
        inclusion-subuniverse P X ≃
        ( inclusion-subuniverse P (pr1 x) +
          ( inclusion-subuniverse P (pr1 (pr2 x)) +
            inclusion-subuniverse P (pr2 (pr2 x)))))

  module _
    (d : ternary-coproduct-Decomposition-subuniverse)
    where

    types-ternary-coproduct-Decomposition-subuniverse :
      type-subuniverse P × (type-subuniverse P × type-subuniverse P)
    types-ternary-coproduct-Decomposition-subuniverse = pr1 d

    first-summand-ternary-coproduct-Decomposition-subuniverse :
      type-subuniverse P
    first-summand-ternary-coproduct-Decomposition-subuniverse =
      ( pr1 types-ternary-coproduct-Decomposition-subuniverse)

    second-summand-ternary-coproduct-Decomposition-subuniverse :
      type-subuniverse P
    second-summand-ternary-coproduct-Decomposition-subuniverse =
      ( pr1 (pr2 types-ternary-coproduct-Decomposition-subuniverse))

    third-summand-ternary-coproduct-Decomposition-subuniverse :
      type-subuniverse P
    third-summand-ternary-coproduct-Decomposition-subuniverse =
      ( pr2 (pr2 types-ternary-coproduct-Decomposition-subuniverse))

    matching-correspondence-ternary-coproductuct-Decomposition-subuniverse :
      ( inclusion-subuniverse P X) ≃
      ( ( inclusion-subuniverse P
          first-summand-ternary-coproduct-Decomposition-subuniverse) +
        ( ( inclusion-subuniverse P
            second-summand-ternary-coproduct-Decomposition-subuniverse) +
          ( inclusion-subuniverse P
            third-summand-ternary-coproduct-Decomposition-subuniverse)))
    matching-correspondence-ternary-coproductuct-Decomposition-subuniverse =
      pr2 d
```

## Propositions

### Characterization of equality of binary coproduct Decomposition of subuniverse

```agda
equiv-binary-coproduct-Decomposition-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P)
  (X : binary-coproduct-Decomposition-subuniverse P A)
  (Y : binary-coproduct-Decomposition-subuniverse P A) →
  UU (l1)
equiv-binary-coproduct-Decomposition-subuniverse P A X Y =
  Σ ( type-left-summand-binary-coproduct-Decomposition-subuniverse P A X ≃
      type-left-summand-binary-coproduct-Decomposition-subuniverse P A Y)
    ( λ el →
      Σ ( type-right-summand-binary-coproduct-Decomposition-subuniverse P A X ≃
          type-right-summand-binary-coproduct-Decomposition-subuniverse P A Y)
        ( λ er →
          ( map-coproduct (map-equiv el) (map-equiv er) ∘
            map-equiv
              ( matching-correspondence-binary-coproduct-Decomposition-subuniverse
                  P A X)) ~
          ( map-equiv
            ( matching-correspondence-binary-coproduct-Decomposition-subuniverse
                P A Y))))

module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P)
  (X : binary-coproduct-Decomposition-subuniverse P A)
  (Y : binary-coproduct-Decomposition-subuniverse P A)
  (e : equiv-binary-coproduct-Decomposition-subuniverse P A X Y)
  where

  equiv-left-summand-equiv-binary-coproduct-Decomposition-subuniverse :
    type-left-summand-binary-coproduct-Decomposition-subuniverse P A X ≃
    type-left-summand-binary-coproduct-Decomposition-subuniverse P A Y
  equiv-left-summand-equiv-binary-coproduct-Decomposition-subuniverse = pr1 e

  map-equiv-left-summand-equiv-binary-coproduct-Decomposition-subuniverse :
    type-left-summand-binary-coproduct-Decomposition-subuniverse P A X →
    type-left-summand-binary-coproduct-Decomposition-subuniverse P A Y
  map-equiv-left-summand-equiv-binary-coproduct-Decomposition-subuniverse =
    map-equiv
      equiv-left-summand-equiv-binary-coproduct-Decomposition-subuniverse

  equiv-right-summand-equiv-binary-coproduct-Decomposition-subuniverse :
    type-right-summand-binary-coproduct-Decomposition-subuniverse P A X ≃
    type-right-summand-binary-coproduct-Decomposition-subuniverse P A Y
  equiv-right-summand-equiv-binary-coproduct-Decomposition-subuniverse =
    pr1 (pr2 e)

  map-equiv-right-summand-equiv-binary-coproduct-Decomposition-subuniverse :
    type-right-summand-binary-coproduct-Decomposition-subuniverse P A X →
    type-right-summand-binary-coproduct-Decomposition-subuniverse P A Y
  map-equiv-right-summand-equiv-binary-coproduct-Decomposition-subuniverse =
    map-equiv
      equiv-right-summand-equiv-binary-coproduct-Decomposition-subuniverse

module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P)
  (X : binary-coproduct-Decomposition-subuniverse P A)
  where

  id-equiv-binary-coproduct-Decomposition-subuniverse :
    equiv-binary-coproduct-Decomposition-subuniverse P A X X
  pr1 id-equiv-binary-coproduct-Decomposition-subuniverse = id-equiv
  pr1 (pr2 id-equiv-binary-coproduct-Decomposition-subuniverse) = id-equiv
  pr2 (pr2 id-equiv-binary-coproduct-Decomposition-subuniverse) x =
    id-map-coproduct
      ( type-left-summand-binary-coproduct-Decomposition-subuniverse P A X)
      ( type-right-summand-binary-coproduct-Decomposition-subuniverse P A X)
      ( map-equiv
        ( matching-correspondence-binary-coproduct-Decomposition-subuniverse
          P A X)
        ( x))

  is-torsorial-equiv-binary-coproduct-Decomposition-subuniverse :
    is-torsorial (equiv-binary-coproduct-Decomposition-subuniverse P A X)
  is-torsorial-equiv-binary-coproduct-Decomposition-subuniverse =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv-subuniverse P
        ( left-summand-binary-coproduct-Decomposition-subuniverse P A X))
      ( left-summand-binary-coproduct-Decomposition-subuniverse P A X ,
        id-equiv)
      ( is-torsorial-Eq-structure
        ( is-torsorial-equiv-subuniverse P
          ( right-summand-binary-coproduct-Decomposition-subuniverse P A X))
        ( right-summand-binary-coproduct-Decomposition-subuniverse P A X ,
          id-equiv)
        ( is-torsorial-htpy-equiv
          ( equiv-coproduct id-equiv id-equiv ∘e
            matching-correspondence-binary-coproduct-Decomposition-subuniverse
              P A X)))

  equiv-eq-binary-coproduct-Decomposition-subuniverse :
    (Y : binary-coproduct-Decomposition-subuniverse P A) → (X ＝ Y) →
    equiv-binary-coproduct-Decomposition-subuniverse P A X Y
  equiv-eq-binary-coproduct-Decomposition-subuniverse .X refl =
    id-equiv-binary-coproduct-Decomposition-subuniverse

  is-equiv-equiv-eq-binary-coproduct-Decomposition-subuniverse :
    (Y : binary-coproduct-Decomposition-subuniverse P A) →
    is-equiv (equiv-eq-binary-coproduct-Decomposition-subuniverse Y)
  is-equiv-equiv-eq-binary-coproduct-Decomposition-subuniverse =
    fundamental-theorem-id
      is-torsorial-equiv-binary-coproduct-Decomposition-subuniverse
      equiv-eq-binary-coproduct-Decomposition-subuniverse

  extensionality-binary-coproduct-Decomposition-subuniverse :
    (Y : binary-coproduct-Decomposition-subuniverse P A) →
    (X ＝ Y) ≃ equiv-binary-coproduct-Decomposition-subuniverse P A X Y
  pr1 (extensionality-binary-coproduct-Decomposition-subuniverse Y) =
    equiv-eq-binary-coproduct-Decomposition-subuniverse Y
  pr2 (extensionality-binary-coproduct-Decomposition-subuniverse Y) =
    is-equiv-equiv-eq-binary-coproduct-Decomposition-subuniverse Y

  eq-equiv-binary-coproduct-Decomposition-subuniverse :
    (Y : binary-coproduct-Decomposition-subuniverse P A) →
    equiv-binary-coproduct-Decomposition-subuniverse P A X Y → (X ＝ Y)
  eq-equiv-binary-coproduct-Decomposition-subuniverse Y =
    map-inv-equiv (extensionality-binary-coproduct-Decomposition-subuniverse Y)
```

### Equivalence between binary coproduct Decomposition-subuniverse induce by commutativiy of coproduct

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  equiv-commutative-binary-coproduct-Decomposition-subuniverse :
    binary-coproduct-Decomposition-subuniverse P X ≃
    binary-coproduct-Decomposition-subuniverse P X
  equiv-commutative-binary-coproduct-Decomposition-subuniverse =
    ( associative-Σ) ∘e
    ( ( equiv-Σ
        ( _)
        ( commutative-product)
        ( λ x →
          equiv-postcomp-equiv
            ( commutative-coproduct
              ( inclusion-subuniverse P (pr1 x))
              ( inclusion-subuniverse P (pr2 x)))
            (inclusion-subuniverse P X))) ∘e
      ( ( inv-associative-Σ)))
```

### Equivalence between iterated coproduct and ternary coproduct decomposition

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  (C1 : is-closed-under-coproducts-subuniverse P)
  where

  private
    map-reassociate-left-iterated-coproduct-Decomposition-subuniverse :
      left-iterated-binary-coproduct-Decomposition-subuniverse P X →
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ A →
                  ( inclusion-subuniverse P A) ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) +
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ A →
              ( inclusion-subuniverse P X) ≃
              ( inclusion-subuniverse P (pr1 A) +
                inclusion-subuniverse P (pr1 x))))
    map-reassociate-left-iterated-coproduct-Decomposition-subuniverse
      ( (A , B , e) , C , D , f) =
      ( (B , C , D) , (A , f) , e)

    map-inv-reassociate-left-iterated-coproduct-Decomposition-subuniverse :
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
      left-iterated-binary-coproduct-Decomposition-subuniverse P X
    map-inv-reassociate-left-iterated-coproduct-Decomposition-subuniverse
      ( (B , C , D) , (A , f) , e) =
      ( (A , B , e) , C , D , f)

    equiv-reassociate-left-iterated-coproduct-Decomposition-subuniverse :
      left-iterated-binary-coproduct-Decomposition-subuniverse P X ≃
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
    pr1 equiv-reassociate-left-iterated-coproduct-Decomposition-subuniverse =
      map-reassociate-left-iterated-coproduct-Decomposition-subuniverse
    pr2 equiv-reassociate-left-iterated-coproduct-Decomposition-subuniverse =
      is-equiv-is-invertible
        map-inv-reassociate-left-iterated-coproduct-Decomposition-subuniverse
        refl-htpy
        refl-htpy

  equiv-ternary-left-iterated-coproduct-Decomposition-subuniverse :
    left-iterated-binary-coproduct-Decomposition-subuniverse P X ≃
    ternary-coproduct-Decomposition-subuniverse P X
  equiv-ternary-left-iterated-coproduct-Decomposition-subuniverse =
    ( equiv-tot
      ( λ x →
        ( ( equiv-postcomp-equiv
            ( commutative-coproduct _ _)
            ( inclusion-subuniverse P X)) ∘e
        ( ( left-unit-law-Σ-is-contr
            ( is-torsorial-equiv-subuniverse' P
              ( ( inclusion-subuniverse P (pr1 (pr2 x)) +
                  inclusion-subuniverse P (pr2 (pr2 x))) ,
                ( C1 (pr2 (pr1 (pr2 x))) (pr2 (pr2 (pr2 x)))))))
            ( ( ( inclusion-subuniverse P (pr1 (pr2 x)) +
                  inclusion-subuniverse P (pr2 (pr2 x))) ,
                ( C1 (pr2 (pr1 (pr2 x))) (pr2 (pr2 (pr2 x))))) ,
              ( id-equiv)))))) ∘e
    ( equiv-reassociate-left-iterated-coproduct-Decomposition-subuniverse)

  private
    map-reassociate-right-iterated-coproduct-Decomposition-subuniverse :
      right-iterated-binary-coproduct-Decomposition-subuniverse P X →
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ B →
                  ( inclusion-subuniverse P B) ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) +
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ B →
              ( inclusion-subuniverse P X) ≃
              ( inclusion-subuniverse P (pr1 x) +
                inclusion-subuniverse P (pr1 B))))
    map-reassociate-right-iterated-coproduct-Decomposition-subuniverse
      ( (A , B , e) , C , D , f) =
      ( (A , C , D) , (B , f) , e)

    map-inv-reassociate-right-iterated-coproduct-Decomposition-subuniverse :
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ B →
                  ( inclusion-subuniverse P B) ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) +
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ B →
              ( inclusion-subuniverse P X) ≃
              ( inclusion-subuniverse P (pr1 x) +
                inclusion-subuniverse P (pr1 B)))) →
      right-iterated-binary-coproduct-Decomposition-subuniverse P X
    map-inv-reassociate-right-iterated-coproduct-Decomposition-subuniverse
      ( (A , C , D) , (B , f) , e) =
      ( (A , B , e) , C , D , f)

    equiv-reassociate-right-iterated-coproduct-Decomposition-subuniverse :
      right-iterated-binary-coproduct-Decomposition-subuniverse P X ≃
      Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
        ( λ x →
          Σ ( Σ ( type-subuniverse P)
                ( λ B →
                  ( inclusion-subuniverse P B) ≃
                  ( inclusion-subuniverse P (pr1 (pr2 x)) +
                    inclusion-subuniverse P (pr2 (pr2 x)))))
            ( λ B →
              ( inclusion-subuniverse P X) ≃
              ( inclusion-subuniverse P (pr1 x) +
                inclusion-subuniverse P (pr1 B))))
    pr1 equiv-reassociate-right-iterated-coproduct-Decomposition-subuniverse =
      map-reassociate-right-iterated-coproduct-Decomposition-subuniverse
    pr2 equiv-reassociate-right-iterated-coproduct-Decomposition-subuniverse =
      is-equiv-is-invertible
        map-inv-reassociate-right-iterated-coproduct-Decomposition-subuniverse
        refl-htpy
        refl-htpy

  equiv-ternary-right-iterated-coproduct-Decomposition-subuniverse :
    right-iterated-binary-coproduct-Decomposition-subuniverse P X ≃
    ternary-coproduct-Decomposition-subuniverse P X
  equiv-ternary-right-iterated-coproduct-Decomposition-subuniverse =
    ( equiv-tot
      ( λ x →
        left-unit-law-Σ-is-contr
          ( is-torsorial-equiv-subuniverse' P
            ( ( inclusion-subuniverse P (pr1 (pr2 x)) +
                inclusion-subuniverse P (pr2 (pr2 x))) ,
              ( C1 (pr2 (pr1 (pr2 x))) (pr2 (pr2 (pr2 x))))))
          ( ( ( inclusion-subuniverse P (pr1 (pr2 x)) +
                inclusion-subuniverse P (pr2 (pr2 x))) ,
              ( C1 (pr2 (pr1 (pr2 x))) (pr2 (pr2 (pr2 x))))) ,
            ( id-equiv)))) ∘e
    ( equiv-reassociate-right-iterated-coproduct-Decomposition-subuniverse)
```

### Coproduct-decomposition with empty right summand

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  (C1 : is-in-subuniverse P (raise-empty l1))
  where

  equiv-is-empty-right-summand-binary-coproduct-Decomposition-subuniverse :
    Σ ( binary-coproduct-Decomposition-subuniverse P X)
      ( λ d →
        is-empty
          ( inclusion-subuniverse P
            ( right-summand-binary-coproduct-Decomposition-subuniverse
              P X d))) ≃
    Σ ( type-subuniverse P)
      ( λ Y → inclusion-subuniverse P X ≃ pr1 Y)
  equiv-is-empty-right-summand-binary-coproduct-Decomposition-subuniverse =
    ( equiv-tot
      ( λ x →
        ( equiv-postcomp-equiv
          ( right-unit-law-coproduct-is-empty
            ( inclusion-subuniverse P x)
            ( raise-empty l1)
            ( is-empty-raise-empty))
          ( inclusion-subuniverse P X)) ∘e
        ( ( left-unit-law-Σ-is-contr
            ( ( ( raise-empty l1 , C1) , is-empty-raise-empty) ,
              ( λ x →
                eq-pair-Σ
                  ( eq-pair-Σ
                    ( eq-equiv (equiv-is-empty is-empty-raise-empty (pr2 x)))
                    ( eq-type-Prop (P _)))
                  ( eq-is-prop is-property-is-empty)))
            ( ( raise-empty l1 , C1) , is-empty-raise-empty)) ∘e
          ( ( inv-associative-Σ) ∘e
            ( ( equiv-tot (λ _ → commutative-product)) ∘e
              ( ( associative-Σ))))))) ∘e
    ( ( associative-Σ))
```
