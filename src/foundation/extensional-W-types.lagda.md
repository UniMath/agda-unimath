# Extensional W-types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.extensional-W-types where

open import foundation.contractible-types using
  ( is-contr; is-contr-equiv; is-contr-equiv')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.elementhood-relation-W-types using (_∈-𝕎_)
open import foundation.equality-dependent-function-types using
  ( is-contr-total-Eq-Π)
open import foundation.equivalences using
  ( _≃_; id-equiv; map-equiv; is-contr-total-htpy-equiv; is-equiv;
    map-inv-is-equiv; map-inv-equiv; _∘e_; isretr-map-inv-equiv; inv-equiv;
    is-equiv-Prop)
open import foundation.functions using (_∘_)
open import foundation.functoriality-dependent-function-types using
  ( equiv-Π)
open import foundation.functoriality-dependent-pair-types using
  ( equiv-tot; equiv-Σ)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id; fundamental-theorem-id')
open import foundation.homotopies using (_~_; refl-htpy; is-contr-total-htpy)
open import foundation.identity-types using
  ( Id; equiv-concat; ap; equiv-tr; refl)
open import foundation.propositional-truncations using
  ( type-trunc-Prop; apply-universal-property-trunc-Prop)
open import foundation.propositions using (Π-Prop)
open import foundation.slice using (equiv-fam-equiv-equiv-slice)
open import foundation.type-arithmetic-dependent-pair-types using
  ( right-unit-law-Σ-is-contr; equiv-left-swap-Σ; assoc-Σ)
open import foundation.univalent-type-families using (is-univalent)
open import foundation.universe-levels using (Level; UU; _⊔_)
open import foundation.W-types using
  ( 𝕎; tree-𝕎; symbol-𝕎; inv-equiv-structure-𝕎-Alg)
```

## Idea

A W-type `𝕎 A B` is said to be extensional if for any two elements `S T : 𝕎 A B` the induced map

```md
  Id S T → ((U : 𝕎 A B) → (U ∈-𝕎 S) ≃ (U ∈-𝕎 T))
```

is an equivalence.

## Definition

### Extensional equality on W-types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  extensional-Eq-eq-𝕎 : 
    {x y : 𝕎 A B} → Id x y → (z : 𝕎 A B) → (z ∈-𝕎 x) ≃ (z ∈-𝕎 y)
  extensional-Eq-eq-𝕎 refl z = id-equiv

is-extensional-𝕎 :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) → UU (l1 ⊔ l2)
is-extensional-𝕎 A B =
  (x y : 𝕎 A B) → is-equiv (extensional-Eq-eq-𝕎 {x = x} {y})
  
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  Eq-ext-𝕎 : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  Eq-ext-𝕎 x y = (z : 𝕎 A B) → (z ∈-𝕎 x) ≃ (z ∈-𝕎 y)

  refl-Eq-ext-𝕎 : (x : 𝕎 A B) → Eq-ext-𝕎 x x
  refl-Eq-ext-𝕎 x z = id-equiv

  Eq-ext-eq-𝕎 : {x y : 𝕎 A B} → Id x y → Eq-ext-𝕎 x y
  Eq-ext-eq-𝕎 {x} refl = refl-Eq-ext-𝕎 x
```

## Properties

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  Eq-Eq-ext-𝕎 : (x y : 𝕎 A B) (u v : Eq-ext-𝕎 x y) → UU (l1 ⊔ l2)
  Eq-Eq-ext-𝕎 x y u v =
    (z : 𝕎 A B) → map-equiv (u z) ~ map-equiv (v z)

  refl-Eq-Eq-ext-𝕎 : (x y : 𝕎 A B) (u : Eq-ext-𝕎 x y) → Eq-Eq-ext-𝕎 x y u u
  refl-Eq-Eq-ext-𝕎 x y u z = refl-htpy

  is-contr-total-Eq-Eq-ext-𝕎 :
    (x y : 𝕎 A B) (u : Eq-ext-𝕎 x y) →
    is-contr (Σ (Eq-ext-𝕎 x y) (Eq-Eq-ext-𝕎 x y u))
  is-contr-total-Eq-Eq-ext-𝕎 x y u =
    is-contr-total-Eq-Π
      ( λ z e → map-equiv (u z) ~ map-equiv e)
      ( λ z → is-contr-total-htpy-equiv (u z))

  Eq-Eq-ext-eq-𝕎 :
    (x y : 𝕎 A B) (u v : Eq-ext-𝕎 x y) → Id u v → Eq-Eq-ext-𝕎 x y u v
  Eq-Eq-ext-eq-𝕎 x y u .u refl = refl-Eq-Eq-ext-𝕎 x y u

  is-equiv-Eq-Eq-ext-eq-𝕎 :
    (x y : 𝕎 A B) (u v : Eq-ext-𝕎 x y) → is-equiv (Eq-Eq-ext-eq-𝕎 x y u v)
  is-equiv-Eq-Eq-ext-eq-𝕎 x y u =
    fundamental-theorem-id u
      ( refl-Eq-Eq-ext-𝕎 x y u)
      ( is-contr-total-Eq-Eq-ext-𝕎 x y u)
      ( Eq-Eq-ext-eq-𝕎 x y u)

  eq-Eq-Eq-ext-𝕎 :
    {x y : 𝕎 A B} {u v : Eq-ext-𝕎 x y} → Eq-Eq-ext-𝕎 x y u v → Id u v
  eq-Eq-Eq-ext-𝕎 {x} {y} {u} {v} =
    map-inv-is-equiv (is-equiv-Eq-Eq-ext-eq-𝕎 x y u v)

  equiv-total-Eq-ext-𝕎 :
    (x : 𝕎 A B) → Σ (𝕎 A B) (Eq-ext-𝕎 x) ≃ Σ A (λ a → B (symbol-𝕎 x) ≃ B a)
  equiv-total-Eq-ext-𝕎 (tree-𝕎 a f) =
    ( ( equiv-tot
            ( λ x →
              ( ( right-unit-law-Σ-is-contr
                  ( λ e → is-contr-total-htpy (f ∘ map-inv-equiv e))) ∘e
                ( equiv-tot
                  ( λ e →
                    equiv-tot
                      ( λ g →
                        equiv-Π
                          ( λ y → Id (f (map-inv-equiv e y)) (g y))
                          ( e)
                          ( λ y →
                            equiv-concat
                              ( ap f (isretr-map-inv-equiv e y))
                              ( g (map-equiv e y))))))) ∘e
              ( ( equiv-left-swap-Σ) ∘e 
                ( equiv-tot
                  ( λ g →
                    inv-equiv (equiv-fam-equiv-equiv-slice f g)))))) ∘e
          ( assoc-Σ
            ( A)
            ( λ x → B x → 𝕎 A B)
            ( λ t → Eq-ext-𝕎 (tree-𝕎 a f) (tree-𝕎 (pr1 t) (pr2 t))))) ∘e
        ( equiv-Σ
          ( λ (t : Σ A (λ x → B x → 𝕎 A B)) →
            Eq-ext-𝕎 (tree-𝕎 a f) (tree-𝕎 (pr1 t) (pr2 t)))
          ( inv-equiv-structure-𝕎-Alg)
          ( H))
    where
    H : (z : 𝕎 A (λ x → B x)) →
        Eq-ext-𝕎 ( tree-𝕎 a f) z ≃
        Eq-ext-𝕎
          ( tree-𝕎 a f)
          ( tree-𝕎
            ( pr1 (map-equiv inv-equiv-structure-𝕎-Alg z))
            ( pr2 (map-equiv inv-equiv-structure-𝕎-Alg z)))
    H (tree-𝕎 b g) = id-equiv

  is-contr-total-Eq-ext-is-univalent-𝕎 :
    is-univalent B → (x : 𝕎 A B) → is-contr (Σ (𝕎 A B) (Eq-ext-𝕎 x))
  is-contr-total-Eq-ext-is-univalent-𝕎 H (tree-𝕎 a f) =
    is-contr-equiv
      ( Σ A (λ x → B a ≃ B x))
      ( equiv-total-Eq-ext-𝕎 (tree-𝕎 a f))
      ( fundamental-theorem-id' a id-equiv (λ x → equiv-tr B) (H a))

  is-extensional-is-univalent-𝕎 :
    is-univalent B → is-extensional-𝕎 A B
  is-extensional-is-univalent-𝕎 H x =
    fundamental-theorem-id x
      ( λ z → id-equiv)
      ( is-contr-total-Eq-ext-is-univalent-𝕎 H x)
      ( λ y → extensional-Eq-eq-𝕎 {y = y})

  is-univalent-is-extensional-𝕎 :
    type-trunc-Prop (𝕎 A B) → is-extensional-𝕎 A B → is-univalent B
  is-univalent-is-extensional-𝕎 p H x =
    apply-universal-property-trunc-Prop p
      ( Π-Prop A (λ y → is-equiv-Prop (λ (γ : Id x y) → equiv-tr B γ)))
      ( λ w →
        fundamental-theorem-id x
          ( id-equiv)
          ( is-contr-equiv'
            ( Σ (𝕎 A B) (Eq-ext-𝕎 (tree-𝕎 x (λ y → w))))
            ( equiv-total-Eq-ext-𝕎 (tree-𝕎 x (λ y → w)))
            ( fundamental-theorem-id'
              ( tree-𝕎 x (λ y → w))
              ( λ z → id-equiv)
              ( λ z → extensional-Eq-eq-𝕎)
              ( H (tree-𝕎 x (λ y → w)))))
          ( λ y →  equiv-tr B {y = y}))
```
