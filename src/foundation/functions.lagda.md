#  Functions

```agda
-- {-# OPTIONS --safe #-}

module foundation.functions where

open import foundation-core.functions public

open import foundation.dependent-pair-types

open import foundation.equivalences
open import foundation.equivalence-extensionality
open import foundation.equality-dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.univalence
open import foundation.universe-levels
```

## Property

### Type duality

The type of all function from `A → B` is equivalent to the type of function `Y : B → 𝒰` with an equivalence `A ≃ Σ B Y `

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where
  map-type-duality-functions : (A → B) → Σ (B → UU (l1 ⊔ l2)) (λ Y → A ≃ Σ B Y)
  pr1 (map-type-duality-functions f) = fib f
  pr2 (map-type-duality-functions f) = inv-equiv-total-fib f

  map-inv-type-duality-functions :  Σ ((B → UU l2)) (λ Y → A ≃ Σ B Y) → (A → B)
  map-inv-type-duality-functions ( Y , e) = pr1 ∘ map-equiv e

issec-map-inv-type-duality-functions :
  {l1 l2 : Level} {A : UU l1} {B : UU (l1 ⊔ l2)}→
  (map-type-duality-functions A B ∘ map-inv-type-duality-functions A B) ~ id
issec-map-inv-type-duality-functions {A = A} {B = B} (Y , e) =
  eq-pair-Σ
    ( eq-htpy
      ( λ b →
        eq-equiv
          ( Σ A ( λ a → (pr1 ((map-equiv e) a) ＝ b)))
          ( Y b)
          ( equiv-fib-pr1 Y b ∘e
            ( equiv-Σ-equiv-base
                ( λ x → pr1 x ＝ b)
                ( e)))))
    ( eq-htpy-equiv
      ( λ a →
        ( ( ap
            ( λ f → map-equiv f a)
            ( lemma
              ( e)
              ( λ b →
                equiv-fib-pr1 Y b ∘e equiv-Σ-equiv-base (λ x → pr1 x ＝ b) e)
              ( pr2
                ( map-type-duality-functions A B
                  ( map-inv-type-duality-functions A B (Y , e)))))) ∙
          ( eq-pair-Σ refl refl))))
  where
    lemma-tr :
      {l1 l2 : Level} {A : UU l1} {B : UU l2} {Y0 Y1 : B → UU l2} →
      (e : A ≃ Σ B Y1) (p : Y0 ＝ Y1) (h : A ≃ Σ B Y0) →
      ( tr
        ( λ Y → A ≃ Σ B Y)
        ( p)
        ( h)) ＝
      ( equiv-Σ Y1 id-equiv ( λ b → equiv-eq (htpy-eq p b)) ∘e h)
    lemma-tr e refl h =
      ( ( inv (left-unit-law-equiv h)) ∙
        ( ap (λ f → f ∘e h) ( eq-htpy-equiv refl-htpy)))

    lemma :
      {l1 l2 : Level} {A : UU l1} {B : UU l2} {Y0 Y1 : B → UU l2} →
      (e : A ≃ Σ B Y1) (H : (b : B) → (Y0 b ≃ Y1 b)) (h : A ≃ Σ B Y0) →
      ( tr
        ( λ Y → A ≃ Σ B Y)
        ( eq-htpy ( λ b → eq-equiv ( Y0 b) ( Y1 b) ( H b)))
        ( h)) ＝
      ( equiv-Σ Y1 id-equiv ( λ b → H b) ∘e h)
    lemma  {Y0 = Y0} {Y1 = Y1} e H h =
      ( ( lemma-tr
          ( e)
          ( ( eq-htpy ( λ b → eq-equiv ( Y0 b) ( Y1 b) ( H b))))
          ( h)) ∙
        ( ap
          ( λ p → equiv-Σ Y1 id-equiv p ∘e h )
          ( ( ap
              ( λ p → equiv-eq ∘ p)
              ( issec-eq-htpy (λ b → eq-equiv (Y0 b) (Y1 b) (H b)))) ∙
            ( eq-htpy
              ( λ b →
                issec-map-inv-is-equiv (univalence (Y0 b) (Y1 b)) (H b))))))

isretr-map-inv-type-duality-functions :
  {l1 l2 : Level} {A : UU l1} {B : UU (l1 ⊔ l2)}→
  (map-inv-type-duality-functions A B ∘ map-type-duality-functions A B) ~ id
isretr-map-inv-type-duality-functions = refl-htpy

is-equiv-map-type-duality-functions :
  {l1 : Level} (l2 : Level) (A : UU l1) (B : UU (l1 ⊔ l2)) →
  is-equiv (map-type-duality-functions A B)
is-equiv-map-type-duality-functions l2 A B =
  is-equiv-has-inverse
    ( map-inv-type-duality-functions A B)
    ( issec-map-inv-type-duality-functions {l2 = l2})
    ( isretr-map-inv-type-duality-functions {l2 = l2})

type-duality-functions :
  {l1 : Level} (l2 : Level) (A : UU l1) (B : UU (l1 ⊔ l2))→
  (A → B) ≃ Σ (B → UU (l1 ⊔ l2)) (λ Y → A ≃ Σ B Y)
pr1 (type-duality-functions l2 A B) = map-type-duality-functions A B
pr2 (type-duality-functions l2 A B) = is-equiv-map-type-duality-functions l2 A B
```
