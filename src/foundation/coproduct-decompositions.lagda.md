# Coproduct decompositions

```agda
module foundation.coproduct-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-decompositions-subuniverse
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.function-extensionality
open import foundation.functoriality-coproduct-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.structure-identity-principle
open import foundation.transposition-identifications-along-equivalences
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Definitions

### Binary coproduct decompositions

```agda
module _
  {l1 : Level} (l2 l3 : Level) (X : UU l1)
  where

  binary-coproduct-Decomposition : UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
  binary-coproduct-Decomposition =
    Σ (UU l2) (λ A → Σ (UU l3) (λ B → X ≃ A + B))

module _
  {l1 l2 l3 : Level} {X : UU l1}
  (d : binary-coproduct-Decomposition l2 l3 X)
  where

  left-summand-binary-coproduct-Decomposition : UU l2
  left-summand-binary-coproduct-Decomposition = pr1 d

  right-summand-binary-coproduct-Decomposition : UU l3
  right-summand-binary-coproduct-Decomposition = pr1 (pr2 d)

  matching-correspondence-binary-coproduct-Decomposition :
    X ≃
    left-summand-binary-coproduct-Decomposition +
    right-summand-binary-coproduct-Decomposition
  matching-correspondence-binary-coproduct-Decomposition = pr2 (pr2 d)

  map-matching-correspondence-binary-coproduct-Decomposition :
    X →
    left-summand-binary-coproduct-Decomposition +
    right-summand-binary-coproduct-Decomposition
  map-matching-correspondence-binary-coproduct-Decomposition =
    map-equiv matching-correspondence-binary-coproduct-Decomposition

  map-inv-matching-correspondence-binary-coproduct-Decomposition :
    left-summand-binary-coproduct-Decomposition +
    right-summand-binary-coproduct-Decomposition →
    X
  map-inv-matching-correspondence-binary-coproduct-Decomposition =
    map-inv-equiv matching-correspondence-binary-coproduct-Decomposition
```

## Propositions

### Coproduct decomposition is equivalent to coproduct decomposition of a full subuniverse

```agda
equiv-coproduct-Decomposition-full-subuniverse :
  {l1 : Level} → (X : UU l1) →
  binary-coproduct-Decomposition l1 l1 X ≃
  binary-coproduct-Decomposition-subuniverse (λ _ → unit-Prop) (X , star)
pr1 (equiv-coproduct-Decomposition-full-subuniverse X) d =
  ( left-summand-binary-coproduct-Decomposition d , star) ,
  ( right-summand-binary-coproduct-Decomposition d , star) ,
  ( matching-correspondence-binary-coproduct-Decomposition d)
pr2 (equiv-coproduct-Decomposition-full-subuniverse X) =
  is-equiv-is-invertible
    ( λ d →
      type-left-summand-binary-coproduct-Decomposition-subuniverse
        ( λ _ → unit-Prop)
        ( X , star)
        ( d) ,
      type-right-summand-binary-coproduct-Decomposition-subuniverse
        ( λ _ → unit-Prop)
        ( X , star)
        ( d) ,
      matching-correspondence-binary-coproduct-Decomposition-subuniverse
        ( λ _ → unit-Prop)
        ( X , star)
        ( d))
    ( λ d →
      eq-equiv-binary-coproduct-Decomposition-subuniverse
        ( λ _ → unit-Prop)
        ( X , star)
        ( _)
        ( d)
        ( id-equiv ,
          ( id-equiv ,
            right-whisker-comp
              ( id-map-coproduct _ _)
              ( map-matching-correspondence-binary-coproduct-Decomposition-subuniverse
                ( λ _ → unit-Prop)
                ( X , star)
                ( d)))))
    ( refl-htpy)
```

### Characterization of equality of binary coproduct decompositions

```agda
equiv-binary-coproduct-Decomposition :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : binary-coproduct-Decomposition l2 l3 A)
  (Y : binary-coproduct-Decomposition l4 l5 A) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
equiv-binary-coproduct-Decomposition X Y =
  Σ ( left-summand-binary-coproduct-Decomposition X ≃
      left-summand-binary-coproduct-Decomposition Y)
    ( λ el →
      Σ ( right-summand-binary-coproduct-Decomposition X ≃
          right-summand-binary-coproduct-Decomposition Y)
        ( λ er →
          ( map-coproduct (map-equiv el) (map-equiv er) ∘
            map-matching-correspondence-binary-coproduct-Decomposition X) ~
          ( map-matching-correspondence-binary-coproduct-Decomposition Y)))

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1}
  (X : binary-coproduct-Decomposition l2 l3 A)
  (Y : binary-coproduct-Decomposition l4 l5 A)
  (e : equiv-binary-coproduct-Decomposition X Y)
  where

  equiv-left-summand-equiv-binary-coproduct-Decomposition :
    left-summand-binary-coproduct-Decomposition X ≃
    left-summand-binary-coproduct-Decomposition Y
  equiv-left-summand-equiv-binary-coproduct-Decomposition = pr1 e

  map-equiv-left-summand-equiv-binary-coproduct-Decomposition :
    left-summand-binary-coproduct-Decomposition X →
    left-summand-binary-coproduct-Decomposition Y
  map-equiv-left-summand-equiv-binary-coproduct-Decomposition =
    map-equiv equiv-left-summand-equiv-binary-coproduct-Decomposition

  equiv-right-summand-equiv-binary-coproduct-Decomposition :
    right-summand-binary-coproduct-Decomposition X ≃
    right-summand-binary-coproduct-Decomposition Y
  equiv-right-summand-equiv-binary-coproduct-Decomposition = pr1 (pr2 e)

  map-equiv-right-summand-equiv-binary-coproduct-Decomposition :
    right-summand-binary-coproduct-Decomposition X →
    right-summand-binary-coproduct-Decomposition Y
  map-equiv-right-summand-equiv-binary-coproduct-Decomposition =
    map-equiv (equiv-right-summand-equiv-binary-coproduct-Decomposition)

module _
  {l1 l2 l3 : Level} {A : UU l1} (X : binary-coproduct-Decomposition l2 l3 A)
  where

  id-equiv-binary-coproduct-Decomposition :
    equiv-binary-coproduct-Decomposition X X
  pr1 id-equiv-binary-coproduct-Decomposition =
    id-equiv
  pr1 (pr2 id-equiv-binary-coproduct-Decomposition) =
    id-equiv
  pr2 (pr2 id-equiv-binary-coproduct-Decomposition) x =
    id-map-coproduct
      ( left-summand-binary-coproduct-Decomposition X)
      ( right-summand-binary-coproduct-Decomposition X)
      ( map-matching-correspondence-binary-coproduct-Decomposition X x)

  abstract
    is-torsorial-equiv-binary-coproduct-Decomposition :
      is-torsorial
        ( equiv-binary-coproduct-Decomposition {l1} {l2} {l3} {l2} {l3} X)
    is-torsorial-equiv-binary-coproduct-Decomposition =
      is-torsorial-Eq-structure
        ( is-torsorial-equiv (left-summand-binary-coproduct-Decomposition X))
        ( left-summand-binary-coproduct-Decomposition X , id-equiv)
        ( is-torsorial-Eq-structure
          ( is-torsorial-equiv (right-summand-binary-coproduct-Decomposition X))
          ( right-summand-binary-coproduct-Decomposition X , id-equiv)
          ( is-torsorial-htpy-equiv
            ( equiv-coproduct id-equiv id-equiv ∘e
              matching-correspondence-binary-coproduct-Decomposition X)))

  equiv-eq-binary-coproduct-Decomposition :
    (Y : binary-coproduct-Decomposition l2 l3 A) →
    (X ＝ Y) →
    equiv-binary-coproduct-Decomposition X Y
  equiv-eq-binary-coproduct-Decomposition .X refl =
    id-equiv-binary-coproduct-Decomposition

  abstract
    is-equiv-equiv-eq-binary-coproduct-Decomposition :
      (Y : binary-coproduct-Decomposition l2 l3 A) →
      is-equiv (equiv-eq-binary-coproduct-Decomposition Y)
    is-equiv-equiv-eq-binary-coproduct-Decomposition =
      fundamental-theorem-id
        ( is-torsorial-equiv-binary-coproduct-Decomposition)
        ( equiv-eq-binary-coproduct-Decomposition)

  extensionality-binary-coproduct-Decomposition :
    (Y : binary-coproduct-Decomposition l2 l3 A) →
    (X ＝ Y) ≃ equiv-binary-coproduct-Decomposition X Y
  pr1 (extensionality-binary-coproduct-Decomposition Y) =
    equiv-eq-binary-coproduct-Decomposition Y
  pr2 (extensionality-binary-coproduct-Decomposition Y) =
    is-equiv-equiv-eq-binary-coproduct-Decomposition Y

  eq-equiv-binary-coproduct-Decomposition :
    (Y : binary-coproduct-Decomposition l2 l3 A) →
    equiv-binary-coproduct-Decomposition X Y → (X ＝ Y)
  eq-equiv-binary-coproduct-Decomposition Y =
    map-inv-equiv (extensionality-binary-coproduct-Decomposition Y)
```

### Equivalence between `X → Fin 2` and `binary-coproduct-Decomposition l1 l1 X`

```agda
module _
  {l1 : Level} {X : UU l1} (f : X → Fin 2)
  where

  matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2 :
    X ≃ fiber f (inl (inr star)) + fiber f (inr star)
  matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2 =
    ( equiv-coproduct
      ( left-unit-law-Σ-is-contr (is-contr-Fin-1) (inr star))
      ( left-unit-law-Σ-is-contr is-contr-unit star)) ∘e
    ( right-distributive-Σ-coproduct (λ x → fiber f x)) ∘e
    ( inv-equiv-total-fiber f)

  map-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2 :
    X → fiber f (inl (inr star)) + fiber f (inr star)
  map-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2 =
    map-equiv
      ( matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2)

  map-inv-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2 :
    fiber f (inl (inr star)) + fiber f (inr star) → X
  map-inv-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2 =
    map-inv-equiv
      ( matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2)

  compute-left-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2 :
    (x : X) →
    (inl (inr star) ＝ f x) →
    Σ ( Σ ( fiber f (inl (inr star)))
          ( λ y →
            inl y ＝
            map-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
              ( x)))
      ( λ z → pr1 (pr1 z) ＝ x)
  compute-left-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
    x p =
    tr
      ( λ a →
        Σ ( Σ ( fiber f (inl (inr star)))
              ( λ y →
                inl y ＝
                ( map-coproduct
                  ( map-left-unit-law-Σ-is-contr
                    ( is-contr-Fin-1)
                    ( inr star))
                  ( map-left-unit-law-Σ-is-contr is-contr-unit star))
                ( map-right-distributive-Σ-coproduct
                  ( λ x → fiber f x)
                  ( pr1 a , x , pr2 a))))
          ( λ z → pr1 (pr1 z) ＝ x))
      ( eq-pair-Σ p (tr-Id-right p (inv p) ∙ left-inv p))
      ( ( ( x , inv p) ,
          ( ap
            ( inl)
            ( inv
              ( map-inv-eq-transpose-equiv
                ( left-unit-law-Σ-is-contr is-contr-Fin-1 (inr star))
                ( refl))))) ,
        ( refl))

  compute-left-inv-matching-correspondence-binary-coporducd-Decomposition-map-into-Fin-2 :
    (y : fiber f (inl (inr star))) →
    pr1 y ＝
    map-inv-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
      ( inl y)
  compute-left-inv-matching-correspondence-binary-coporducd-Decomposition-map-into-Fin-2
    y =
    map-eq-transpose-equiv
      ( matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2)
      ( ( inv
          ( pr2
            ( pr1
              ( compute-left-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
                ( pr1 y)
                ( inv (pr2 y)))))) ∙
        ( ap
            ( inl)
            ( eq-pair-Σ
              ( pr2
                ( compute-left-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
                  ( pr1 y)
                  ( inv (pr2 y))))
              ( eq-is-prop (is-set-Fin 2 _ _)))))

  compute-right-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2 :
    (x : X) →
    (inr star ＝ f x) →
    Σ ( Σ ( fiber f (inr star))
          ( λ y →
            inr y ＝
            map-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
              ( x)))
      ( λ z → pr1 (pr1 z) ＝ x)
  compute-right-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
    x p =
    tr
      ( λ a →
        Σ ( Σ ( fiber f (inr star))
              ( λ y →
                inr y ＝
                ( map-coproduct
                  ( map-left-unit-law-Σ-is-contr
                    ( is-contr-Fin-1)
                    ( inr star))
                  ( map-left-unit-law-Σ-is-contr is-contr-unit star))
                ( map-right-distributive-Σ-coproduct
                  ( λ x → fiber f x)
                  ( pr1 a , x , pr2 a))))
          ( λ z → pr1 (pr1 z) ＝ x))
      ( eq-pair-Σ p (tr-Id-right p (inv p) ∙ left-inv p))
      ( ( ( x , (inv p)) ,
          ( ap
            ( inr)
            ( inv
                ( map-inv-eq-transpose-equiv
                  ( left-unit-law-Σ-is-contr is-contr-unit star)
                  ( refl))))) ,
        ( refl))

  compute-right-inv-matching-correspondence-binary-coporducd-Decomposition-map-into-Fin-2 :
    (y : fiber f (inr star)) →
    pr1 y ＝
    map-inv-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
      ( inr y)
  compute-right-inv-matching-correspondence-binary-coporducd-Decomposition-map-into-Fin-2
    y =
    map-eq-transpose-equiv
      ( matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2)
      ( inv
        ( pr2
          ( pr1
            ( compute-right-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
              ( pr1 y)
              ( inv (pr2 y))))) ∙
        ap
          inr
          ( eq-pair-Σ
            ( pr2
              ( compute-right-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
                ( pr1 y)
                ( inv (pr2 y))))
            ( eq-is-prop (is-set-Fin 2 (f (pr1 y)) (inr star)))))

  map-equiv-binary-coproduct-Decomposition-map-into-Fin-2 :
    binary-coproduct-Decomposition l1 l1 X
  pr1 (map-equiv-binary-coproduct-Decomposition-map-into-Fin-2) =
    fiber f (inl (inr star))
  pr1 (pr2 (map-equiv-binary-coproduct-Decomposition-map-into-Fin-2)) =
    fiber f (inr star)
  pr2 (pr2 (map-equiv-binary-coproduct-Decomposition-map-into-Fin-2)) =
    matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2

module _
  {l1 : Level} {X : UU l1}
  where

  map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper :
    (d : binary-coproduct-Decomposition l1 l1 X) →
    left-summand-binary-coproduct-Decomposition d +
    right-summand-binary-coproduct-Decomposition d →
    Fin 2
  map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
    d (inl _) =
    inl (inr star)
  map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
    d (inr _) =
    inr star

  map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 :
    binary-coproduct-Decomposition l1 l1 X → X → Fin 2
  map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 d x =
    map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
      ( d)
      ( map-matching-correspondence-binary-coproduct-Decomposition d x)

  compute-left-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper :
    (d : binary-coproduct-Decomposition l1 l1 X) →
    (t :
      ( left-summand-binary-coproduct-Decomposition d) +
      ( right-summand-binary-coproduct-Decomposition d)) →
    ( inl (inr star) ＝
      map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
        ( d)
        ( t)) →
    Σ ( left-summand-binary-coproduct-Decomposition d)
      ( λ a → inl a ＝ t)
  compute-left-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
    d (inl y) x =
    y , refl

  compute-left-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 :
    (d : binary-coproduct-Decomposition l1 l1 X) →
    (x : X) →
    ( inl (inr star) ＝
      map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 d x) →
    Σ ( left-summand-binary-coproduct-Decomposition d)
      ( λ a →
        inl a ＝
        map-matching-correspondence-binary-coproduct-Decomposition d x)
  compute-left-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
    d x p =
    compute-left-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
      ( d)
      ( map-matching-correspondence-binary-coproduct-Decomposition d x)
      ( p)

  compute-right-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper :
    (d : binary-coproduct-Decomposition l1 l1 X) →
    (t :
      ( left-summand-binary-coproduct-Decomposition d) +
      ( right-summand-binary-coproduct-Decomposition d)) →
    ( inr star ＝
      map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
        ( d)
        ( t)) →
    Σ ( right-summand-binary-coproduct-Decomposition d)
      ( λ a → inr a ＝ t)
  compute-right-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
    d (inr y) x =
    y , refl

  compute-right-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 :
    (d : binary-coproduct-Decomposition l1 l1 X) →
    (x : X) →
    ( inr star ＝
      map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 d x) →
    Σ ( right-summand-binary-coproduct-Decomposition d)
      ( λ a →
        inr a ＝
        map-matching-correspondence-binary-coproduct-Decomposition d x)
  compute-right-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
    d x p =
    compute-right-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
      ( d)
      ( map-matching-correspondence-binary-coproduct-Decomposition d x)
      ( p)

  is-retraction-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper :
    (f : X → Fin 2) →
    (x : X) →
    (v : (inl (inr star) ＝ f x) + (inr star ＝ f x)) →
    ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
        ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-2 f) x ＝
      f x)
  is-retraction-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
    f x (inl y) =
    ( inv
      ( ap
          ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
              ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-2 f))
          ( pr2
            ( pr1
              ( compute-left-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
                ( f)
                ( x)
                ( y))))) ∙
      ( y))
  is-retraction-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
    f x (inr y) =
    ( inv
      ( ap
          ( λ p →
            map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
              ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-2 f)
              ( p))
          ( pr2
            ( pr1
              ( compute-right-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
                ( f)
                ( x)
                ( y))))) ∙
      ( y))

  is-retraction-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 :
    is-retraction
      ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-2)
      ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2)
  is-retraction-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
    f =
    eq-htpy
      ( λ x →
        is-retraction-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
          ( f)
          ( x)
          ( map-coproduct
            ( map-left-unit-law-Σ-is-contr is-contr-Fin-1 ( inr star))
            ( map-left-unit-law-Σ-is-contr is-contr-unit star)
            ( map-right-distributive-Σ-coproduct
              ( λ y → y ＝ f x)
              ( f x , refl))))

  equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 :
    (d : binary-coproduct-Decomposition l1 l1 X) →
    left-summand-binary-coproduct-Decomposition
      ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-2
        ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 d)) ≃
    left-summand-binary-coproduct-Decomposition d
  equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
    d =
    ( right-unit-law-coproduct
      ( left-summand-binary-coproduct-Decomposition d)) ∘e
    ( equiv-coproduct
      ( right-unit-law-Σ-is-contr (λ _ → is-contr-unit) ∘e
        equiv-tot
          ( λ _ → extensionality-Fin 2 (inl (inr star)) (inl (inr star))))
      ( right-absorption-Σ (right-summand-binary-coproduct-Decomposition d) ∘e
        equiv-tot (λ _ → extensionality-Fin 2 (inr star) (inl (inr star))))) ∘e
    ( right-distributive-Σ-coproduct
      ( λ y →
        map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
          d y ＝ inl (inr star))) ∘e
    ( equiv-Σ-equiv-base
      ( λ y →
        map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
          d y ＝
        inl (inr star))
      ( matching-correspondence-binary-coproduct-Decomposition d))

  map-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 :
    (d : binary-coproduct-Decomposition l1 l1 X) →
    left-summand-binary-coproduct-Decomposition
      ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-2
        ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 d)) →
    left-summand-binary-coproduct-Decomposition d
  map-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
    d =
    map-equiv
      ( equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
        ( d))

  equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 :
    (d : binary-coproduct-Decomposition l1 l1 X) →
    right-summand-binary-coproduct-Decomposition
      ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-2
        ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 d)) ≃
    right-summand-binary-coproduct-Decomposition d
  equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
    d =
    ( left-unit-law-coproduct
      ( right-summand-binary-coproduct-Decomposition d)) ∘e
    ( equiv-coproduct
      ( right-absorption-Σ (left-summand-binary-coproduct-Decomposition d) ∘e
        equiv-tot (λ _ → extensionality-Fin 2 (inl (inr star)) (inr star)))
      ( right-unit-law-Σ-is-contr (λ _ → is-contr-unit) ∘e
        equiv-tot (λ _ → extensionality-Fin 2 (inr star) (inr star)))) ∘e
    ( ( right-distributive-Σ-coproduct
        ( λ y →
          map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
            d y ＝ inr star)) ∘e
      ( equiv-Σ-equiv-base
        ( λ y →
          ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
            d y) ＝
          ( inr star))
        ( matching-correspondence-binary-coproduct-Decomposition d)))

  map-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 :
    (d : binary-coproduct-Decomposition l1 l1 X) →
    right-summand-binary-coproduct-Decomposition
      ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-2
        ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 d)) →
    right-summand-binary-coproduct-Decomposition d
  map-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
    d =
    map-equiv
      ( equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
        ( d))

  compute-equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 :
    ( d : binary-coproduct-Decomposition l1 l1 X) →
    ( inl ∘
      ( map-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
        ( d))) ~
    ( map-matching-correspondence-binary-coproduct-Decomposition d ∘ pr1)
  compute-equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
    d (x , p) =
    ap
      ( λ x →
        inl
        ( map-equiv
            ( ( right-unit-law-coproduct
                ( left-summand-binary-coproduct-Decomposition d)) ∘e
              ( ( equiv-coproduct
                  ( right-unit-law-Σ-is-contr (λ _ → is-contr-unit) ∘e
                    equiv-tot
                      ( λ _ →
                        extensionality-Fin 2 (inl (inr star)) (inl (inr star))))
                  ( right-absorption-Σ
                      (right-summand-binary-coproduct-Decomposition d) ∘e
                    equiv-tot
                      ( λ _ →
                        extensionality-Fin 2 (inr star) (inl (inr star))))) ∘e
                ( ( right-distributive-Σ-coproduct
                    ( λ y →
                      map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
                        d y ＝
                      inl (inr star))))))
            ( x)))
      ( eq-pair-Σ
        {t =
          pair
            ( inl
              ( pr1
                ( compute-left-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
                    d x (inv p))))
            ( refl)}
          ( inv
            ( pr2
              ( compute-left-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
                ( d)
                ( x)
                ( inv p))))
          ( eq-is-prop
            ( is-set-Fin 2 _ _))) ∙
    ( pr2
        ( compute-left-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
          ( d)
          ( x)
          ( inv p)))

  compute-equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 :
    ( d : binary-coproduct-Decomposition l1 l1 X) →
    ( inr ∘
      ( map-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
        ( d))) ~
    ( map-matching-correspondence-binary-coproduct-Decomposition d ∘ pr1)
  compute-equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
    d (x , p) =
    ap
      ( λ x →
        inr
          ( map-equiv
            ( ( left-unit-law-coproduct
                ( right-summand-binary-coproduct-Decomposition d)) ∘e
              ( ( equiv-coproduct
                  ( right-absorption-Σ
                      ( left-summand-binary-coproduct-Decomposition d) ∘e
                    equiv-tot
                      ( λ _ →
                        extensionality-Fin 2 (inl (inr star)) (inr star)))
                  ( right-unit-law-Σ-is-contr (λ _ → is-contr-unit) ∘e
                    equiv-tot
                      ( λ _ → extensionality-Fin 2 (inr star) (inr star)))) ∘e
                ( ( right-distributive-Σ-coproduct
                    ( λ y →
                      map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
                        d y ＝ inr star)))))
            ( x)))
      ( eq-pair-Σ
        { t =
          ( inr
            ( pr1
              ( compute-right-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
                ( d)
                ( x)
                ( inv p))) ,
            refl)}
        ( inv
          ( pr2
            ( compute-right-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
              ( d)
              ( x)
              ( inv p))))
        ( eq-is-prop
          ( is-set-Fin 2 _ _))) ∙
    ( pr2
      ( compute-right-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
        ( d)
        ( x)
        ( inv p)))

  matching-correspondence-htpy-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper :
    ( d : binary-coproduct-Decomposition l1 l1 X) →
    ( x : X) →
    ( ( inl (inr star) ＝
        ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
          ( d)
          ( x))) +
      ( inr star ＝
        ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
          ( d)
          ( x)))) →
    ( map-coproduct
        ( map-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
          ( d))
        ( map-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
          ( d)) ∘
      map-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
        ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 d))
      ( x) ＝
    map-matching-correspondence-binary-coproduct-Decomposition d x
  matching-correspondence-htpy-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
    d x (inl p) =
    ( ap
      ( map-coproduct
        ( map-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
          ( d))
        ( map-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
          ( d)))
      ( inv
        ( pr2
          ( pr1
            ( compute-left-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
              ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
                ( d))
              ( x)
              ( p)))))) ∙
    ( compute-equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
      ( d)
      ( pr1
        ( pr1
          ( pr1
            ( compute-left-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
              ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
                ( d))
              ( x)
              ( p)))) ,
        ( pr2
          ( pr1
            ( pr1
              ( compute-left-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
                ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
                  ( d))
                ( x)
                ( p))))))) ∙
      ( ap
        ( map-matching-correspondence-binary-coproduct-Decomposition d)
        ( pr2
          ( compute-left-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
            ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
              ( d))
            ( x)
            ( p))))
  matching-correspondence-htpy-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
    d x (inr p) =
    ( ap
      ( map-coproduct
        ( map-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
          ( d))
        ( map-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
          ( d)))
      ( inv
        ( pr2
          ( pr1
            ( compute-right-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
              ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
                ( d))
              ( x)
              ( p)))))) ∙
    ( compute-equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
        ( d)
        ( pr1
          ( pr1
            ( pr1
              ( compute-right-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
                ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
                  ( d))
                ( x)
                ( p)))) ,
          pr2
            ( pr1
              ( pr1
                ( compute-right-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
                  ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
                    ( d))
                  ( x)
                  ( p)))))) ∙
      ( ap
        ( map-matching-correspondence-binary-coproduct-Decomposition d)
        ( pr2
          ( compute-right-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
            ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
              ( d))
            ( x)
            ( p))))

  value-map-into-Fin-2-eq-zero-or-one-helper :
    (y : Fin 2) → (inl (inr star) ＝ y) + (inr star ＝ y)
  value-map-into-Fin-2-eq-zero-or-one-helper (inl x) =
    inl (ap inl (eq-is-contr is-contr-Fin-1))
  value-map-into-Fin-2-eq-zero-or-one-helper (inr x) =
    inr (ap inr (eq-is-contr is-contr-unit))

  value-map-into-Fin-2-eq-zero-or-one :
    (f : X → Fin 2) →
    (x : X) →
    (inl (inr star) ＝ f x) + (inr star ＝ f x)
  value-map-into-Fin-2-eq-zero-or-one f x =
    value-map-into-Fin-2-eq-zero-or-one-helper (f x)

  matching-correspondence-htpy-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 :
    ( d : binary-coproduct-Decomposition l1 l1 X) →
    ( map-coproduct
      ( map-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
        ( d)))
    ( map-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
      ( d)) ∘
    ( map-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-2
      ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
        ( d))) ~
    map-matching-correspondence-binary-coproduct-Decomposition d
  matching-correspondence-htpy-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
    d x =
    matching-correspondence-htpy-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2-helper
      ( d)
      ( x)
      ( value-map-into-Fin-2-eq-zero-or-one
        ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 d)
        ( x))

  is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 :
    is-section
    ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-2)
    ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2)
  is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2 d =
    eq-equiv-binary-coproduct-Decomposition
      ( ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-2 ∘
          map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2)
        ( d))
      ( d)
      ( equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
        ( d) ,
        equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
        ( d) ,
        matching-correspondence-htpy-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2
        ( d))

  is-equiv-map-equiv-binary-coproduct-Decomposition-map-into-Fin-2 :
    is-equiv map-equiv-binary-coproduct-Decomposition-map-into-Fin-2
  is-equiv-map-equiv-binary-coproduct-Decomposition-map-into-Fin-2 =
    is-equiv-is-invertible
      ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2)
      ( is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2)
      ( is-retraction-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-2)

  equiv-binary-coproduct-Decomposition-map-into-Fin-2 :
    (X → Fin 2) ≃ binary-coproduct-Decomposition l1 l1 X
  pr1 equiv-binary-coproduct-Decomposition-map-into-Fin-2 =
    map-equiv-binary-coproduct-Decomposition-map-into-Fin-2
  pr2 equiv-binary-coproduct-Decomposition-map-into-Fin-2 =
    is-equiv-map-equiv-binary-coproduct-Decomposition-map-into-Fin-2
```
