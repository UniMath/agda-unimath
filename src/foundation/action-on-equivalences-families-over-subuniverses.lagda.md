# Action on equivalences in type families over subuniverses

```agda
module foundation.action-on-equivalences-families-over-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.sets
open import foundation.subuniverses
open import foundation.transport
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.subtypes
```

</details>

## Ideas

Given a [subuniverse](foundation.subuniverses.md) `P`, any family of types `B`
indexed by types of `P` has an
[action on equivalences](foundation.action-on-equivalences-functions.md)
obtained by using the [univalence axiom](foundation.univalence.md).

## Definition

```agda
module _
  { l1 l2 l3 : Level}
  ( P : subuniverse l1 l2) (B : type-subuniverse P → UU l3)
  where

  action-equiv-family-on-subuniverse :
    (X Y : type-subuniverse P) → pr1 X ≃ pr1 Y → B X ≃ B Y
  action-equiv-family-on-subuniverse X Y e =
    equiv-tr B (eq-equiv-subuniverse P e)
```

## Properties

```agda
  preserves-id-equiv-action-equiv-family-on-subuniverse :
    (X : type-subuniverse P) →
    action-equiv-family-on-subuniverse X X id-equiv ＝ id-equiv
  preserves-id-equiv-action-equiv-family-on-subuniverse X =
    ( ap (equiv-tr B)
      ( is-injective-map-equiv
        ( extensionality-subuniverse P X X)
        ( is-section-map-inv-is-equiv
          ( is-equiv-equiv-eq-subuniverse P X X)
          ( id-equiv)))) ∙
      ( equiv-tr-refl B)

  Ind-path-action-equiv-family-on-subuniverse :
    { l4 : Level}
    ( X : type-subuniverse P)
    ( F : (Y : type-subuniverse P) → B X ≃ B Y → UU l4) →
    F X id-equiv → ( Y : type-subuniverse P) (p : X ＝ Y) →
    F Y (equiv-tr B p)
  Ind-path-action-equiv-family-on-subuniverse X F p .X refl =
    tr (F X) (inv (equiv-tr-refl B)) p

  Ind-action-equiv-family-on-subuniverse :
    { l4 : Level}
    ( X : type-subuniverse P)
    ( F : (Y : type-subuniverse P) → B X ≃ B Y → UU l4) →
    F X id-equiv → (Y : type-subuniverse P) (e : pr1 X ≃ pr1 Y) →
    F Y (action-equiv-family-on-subuniverse X Y e)
  Ind-action-equiv-family-on-subuniverse X F p Y e =
    Ind-path-action-equiv-family-on-subuniverse X F p Y
      ( eq-equiv-subuniverse P e)

  is-contr-preserves-id-action-equiv-family-on-subuniverse :
    ( (X : type-subuniverse P) → is-set (B X)) →
    is-contr
      ( Σ
        ( (X Y : type-subuniverse P) → pr1 X ≃ pr1 Y → B X ≃ B Y)
        ( λ D → (X : type-subuniverse P) → D X X id-equiv ＝ id-equiv))
  pr1 (pr1 (is-contr-preserves-id-action-equiv-family-on-subuniverse H)) =
    action-equiv-family-on-subuniverse
  pr2 (pr1 (is-contr-preserves-id-action-equiv-family-on-subuniverse H)) =
    preserves-id-equiv-action-equiv-family-on-subuniverse
  pr2 (is-contr-preserves-id-action-equiv-family-on-subuniverse H) (D , p) =
    eq-pair-Σ
      ( eq-htpy (λ X → eq-htpy (λ Y → eq-htpy (λ e →
        lemma2 action-equiv-family-on-subuniverse D
          ( λ X →
            preserves-id-equiv-action-equiv-family-on-subuniverse X ∙ inv (p X))
          X Y e))))
      ( eq-is-prop
        ( is-prop-Π
          ( λ X →
            is-set-type-Set
              ( B X ≃ B X , is-set-equiv-is-set (H X) (H X))
              ( D X X id-equiv)
              ( id-equiv))))
    where
    lemma1 :
      (f g : (X Y : UU l1) → (pX : is-in-subuniverse P X) →
        ( pY : is-in-subuniverse P Y) → X ＝ Y →
        B (X , pX) ≃ B (Y , pY)) →
      ( (X : UU l1) (pX : is-in-subuniverse P X)
        (pX' : is-in-subuniverse P X) →
        f X X pX pX' refl ＝ g X X pX pX' refl) →
      ( X Y : UU l1) (pX : is-in-subuniverse P X)
      ( pY : is-in-subuniverse P Y) (p : X ＝ Y) →
      f X Y pX pY p ＝ g X Y pX pY p
    lemma1 f g h X .X pX pX' refl = h X pX pX'
    lemma2 :
      ( f g : (X Y : type-subuniverse P) → pr1 X ≃ pr1 Y → B X ≃ B Y) →
      ( (X : type-subuniverse P) → f X X id-equiv ＝ g X X id-equiv) →
      ( X Y : type-subuniverse P) (e : pr1 X ≃ pr1 Y) →
      f X Y e ＝ g X Y e
    lemma2 f g h X Y e =
      tr
        ( λ e' → f X Y e' ＝ g X Y e')
        ( is-section-map-inv-is-equiv (univalence (pr1 X) (pr1 Y)) e)
        ( lemma1
          ( λ X Y pX pY p → f (X , pX) (Y , pY) (equiv-eq p))
          ( λ X Y pX pY p → g (X , pX) (Y , pY) (equiv-eq p))
          ( λ X pX pX' →
            tr
              ( λ p → f (X , pX) (X , p) id-equiv ＝
                g (X , pX) (X , p) id-equiv)
              ( eq-is-prop (is-prop-is-in-subtype P X))
              ( h ( X , pX)))
          ( pr1 X)
          ( pr1 Y)
          ( pr2 X)
          ( pr2 Y)
          ( eq-equiv (pr1 X) (pr1 Y) e))
```
