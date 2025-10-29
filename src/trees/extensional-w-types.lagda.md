# Extensional W-types

```agda
module trees.extensional-w-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.slice
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalent-type-families
open import foundation.universe-levels

open import trees.elementhood-relation-w-types
open import trees.w-types
```

</details>

## Idea

A W-type `𝕎 A B` is said to be **extensional** if for any two elements
`S T : 𝕎 A B` the induced map

```text
  S ＝ T → ((U : 𝕎 A B) → (U ∈-𝕎 S) ≃ (U ∈-𝕎 T))
```

is an equivalence.

## Definition

### Extensional equality on W-types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  extensional-Eq-eq-𝕎 :
    {x y : 𝕎 A B} → x ＝ y → (z : 𝕎 A B) → (z ∈-𝕎 x) ≃ (z ∈-𝕎 y)
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

  Eq-ext-eq-𝕎 : {x y : 𝕎 A B} → x ＝ y → Eq-ext-𝕎 x y
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

  is-torsorial-Eq-Eq-ext-𝕎 :
    (x y : 𝕎 A B) (u : Eq-ext-𝕎 x y) → is-torsorial (Eq-Eq-ext-𝕎 x y u)
  is-torsorial-Eq-Eq-ext-𝕎 x y u =
    is-torsorial-Eq-Π (λ z → is-torsorial-htpy-equiv (u z))

  Eq-Eq-ext-eq-𝕎 :
    (x y : 𝕎 A B) (u v : Eq-ext-𝕎 x y) → u ＝ v → Eq-Eq-ext-𝕎 x y u v
  Eq-Eq-ext-eq-𝕎 x y u .u refl = refl-Eq-Eq-ext-𝕎 x y u

  is-equiv-Eq-Eq-ext-eq-𝕎 :
    (x y : 𝕎 A B) (u v : Eq-ext-𝕎 x y) → is-equiv (Eq-Eq-ext-eq-𝕎 x y u v)
  is-equiv-Eq-Eq-ext-eq-𝕎 x y u =
    fundamental-theorem-id
      ( is-torsorial-Eq-Eq-ext-𝕎 x y u)
      ( Eq-Eq-ext-eq-𝕎 x y u)

  eq-Eq-Eq-ext-𝕎 :
    {x y : 𝕎 A B} {u v : Eq-ext-𝕎 x y} → Eq-Eq-ext-𝕎 x y u v → u ＝ v
  eq-Eq-Eq-ext-𝕎 {x} {y} {u} {v} =
    map-inv-is-equiv (is-equiv-Eq-Eq-ext-eq-𝕎 x y u v)

  equiv-total-Eq-ext-𝕎 :
    (x : 𝕎 A B) → Σ (𝕎 A B) (Eq-ext-𝕎 x) ≃ Σ A (λ a → B (shape-𝕎 x) ≃ B a)
  equiv-total-Eq-ext-𝕎 (tree-𝕎 a f) =
    ( ( equiv-tot
            ( λ x →
              ( ( right-unit-law-Σ-is-contr
                  ( λ e → is-torsorial-htpy (f ∘ map-inv-equiv e))) ∘e
                ( equiv-tot
                  ( λ e →
                    equiv-tot
                      ( λ g →
                        equiv-Π
                          ( λ y → f (map-inv-equiv e y) ＝ g y)
                          ( e)
                          ( λ y →
                            equiv-concat
                              ( ap f (is-retraction-map-inv-equiv e y))
                              ( g (map-equiv e y))))))) ∘e
              ( ( equiv-left-swap-Σ) ∘e
                ( equiv-tot
                  ( λ g →
                    inv-equiv (equiv-fam-equiv-equiv-slice f g)))))) ∘e
          ( associative-Σ)) ∘e
        ( equiv-Σ
          ( λ (t : Σ A (λ x → B x → 𝕎 A B)) →
            Eq-ext-𝕎 (tree-𝕎 a f) (tree-𝕎 (pr1 t) (pr2 t)))
          ( inv-equiv-structure-𝕎-Alg)
          ( H))
    where
    H :
      ( z : 𝕎 A (λ x → B x)) →
      Eq-ext-𝕎 ( tree-𝕎 a f) z ≃
      Eq-ext-𝕎
        ( tree-𝕎 a f)
        ( tree-𝕎
          ( pr1 (map-equiv inv-equiv-structure-𝕎-Alg z))
          ( pr2 (map-equiv inv-equiv-structure-𝕎-Alg z)))
    H (tree-𝕎 b g) = id-equiv

  is-torsorial-Eq-ext-is-univalent-𝕎 :
    is-univalent B → (x : 𝕎 A B) → is-torsorial (Eq-ext-𝕎 x)
  is-torsorial-Eq-ext-is-univalent-𝕎 H (tree-𝕎 a f) =
    is-contr-equiv
      ( Σ A (λ x → B a ≃ B x))
      ( equiv-total-Eq-ext-𝕎 (tree-𝕎 a f))
      ( fundamental-theorem-id' (λ x → equiv-tr B) (H a))

  is-extensional-is-univalent-𝕎 :
    is-univalent B → is-extensional-𝕎 A B
  is-extensional-is-univalent-𝕎 H x =
    fundamental-theorem-id
      ( is-torsorial-Eq-ext-is-univalent-𝕎 H x)
      ( λ y → extensional-Eq-eq-𝕎 {y = y})

  is-univalent-is-extensional-𝕎 :
    type-trunc-Prop (𝕎 A B) → is-extensional-𝕎 A B → is-univalent B
  is-univalent-is-extensional-𝕎 p H x =
    apply-universal-property-trunc-Prop p
      ( Π-Prop A (λ y → is-equiv-Prop (λ (γ : x ＝ y) → equiv-tr B γ)))
      ( λ w →
        fundamental-theorem-id
          ( is-contr-equiv'
            ( Σ (𝕎 A B) (Eq-ext-𝕎 (tree-𝕎 x (λ y → w))))
            ( equiv-total-Eq-ext-𝕎 (tree-𝕎 x (λ y → w)))
            ( fundamental-theorem-id'
              ( λ z → extensional-Eq-eq-𝕎)
              ( H (tree-𝕎 x (λ y → w)))))
          ( λ y → equiv-tr B {y = y}))
```
