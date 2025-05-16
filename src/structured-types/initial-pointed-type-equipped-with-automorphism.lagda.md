# The initial pointed type equipped with an automorphism

```agda
module structured-types.initial-pointed-type-equipped-with-automorphism where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.iterating-automorphisms
open import foundation.transposition-identifications-along-equivalences
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.pointed-types-equipped-with-automorphisms
```

</details>

## Idea

We show that ℤ is the initial pointed type equipped with an automorphism

## Definition

### The type of integers is the initial type equipped with a point and an automorphism

#### The type of integers is a type equipped with a point and an automorphism

```agda
ℤ-Pointed-Type-With-Aut : Pointed-Type-With-Aut lzero
pr1 (pr1 ℤ-Pointed-Type-With-Aut) = ℤ
pr2 (pr1 ℤ-Pointed-Type-With-Aut) = zero-ℤ
pr2 ℤ-Pointed-Type-With-Aut = equiv-succ-ℤ
```

#### Construction of a map from ℤ into any type with a point and an automorphism

```agda
map-ℤ-Pointed-Type-With-Aut :
  {l : Level} (X : Pointed-Type-With-Aut l) →
  ℤ → type-Pointed-Type-With-Aut X
map-ℤ-Pointed-Type-With-Aut X k =
  map-iterate-automorphism-ℤ k
    ( aut-Pointed-Type-With-Aut X)
    ( point-Pointed-Type-With-Aut X)

preserves-point-map-ℤ-Pointed-Type-With-Aut :
  {l : Level} (X : Pointed-Type-With-Aut l) →
  ( map-ℤ-Pointed-Type-With-Aut X zero-ℤ) ＝
  ( point-Pointed-Type-With-Aut X)
preserves-point-map-ℤ-Pointed-Type-With-Aut X = refl

preserves-aut-map-ℤ-Pointed-Type-With-Aut :
  {l : Level} (X : Pointed-Type-With-Aut l) (k : ℤ) →
  ( map-ℤ-Pointed-Type-With-Aut X (succ-ℤ k)) ＝
  ( map-aut-Pointed-Type-With-Aut X
    ( map-ℤ-Pointed-Type-With-Aut X k))
preserves-aut-map-ℤ-Pointed-Type-With-Aut X k =
  iterate-automorphism-succ-ℤ' k
    ( aut-Pointed-Type-With-Aut X)
    ( point-Pointed-Type-With-Aut X)

hom-ℤ-Pointed-Type-With-Aut :
  {l : Level} (X : Pointed-Type-With-Aut l) →
  hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X
hom-ℤ-Pointed-Type-With-Aut X =
  pair
    ( map-ℤ-Pointed-Type-With-Aut X)
    ( pair
      ( preserves-point-map-ℤ-Pointed-Type-With-Aut X)
      ( preserves-aut-map-ℤ-Pointed-Type-With-Aut X))
```

#### The map previously constructed is unique

```agda
htpy-map-ℤ-Pointed-Type-With-Aut :
  {l : Level} (X : Pointed-Type-With-Aut l)
  (h : hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X) →
  map-ℤ-Pointed-Type-With-Aut X ~
  map-hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X h
htpy-map-ℤ-Pointed-Type-With-Aut X h (inl zero-ℕ) =
  map-eq-transpose-equiv-inv
    ( aut-Pointed-Type-With-Aut X)
    ( ( inv
        ( preserves-point-map-hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut
          X h)) ∙
      ( preserves-aut-map-hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut
        X h neg-one-ℤ))
htpy-map-ℤ-Pointed-Type-With-Aut X h (inl (succ-ℕ k)) =
  map-eq-transpose-equiv-inv
    ( aut-Pointed-Type-With-Aut X)
    ( ( htpy-map-ℤ-Pointed-Type-With-Aut X h (inl k)) ∙
      ( preserves-aut-map-hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut
        X h (inl (succ-ℕ k))))
htpy-map-ℤ-Pointed-Type-With-Aut X h (inr (inl star)) =
  inv
    ( preserves-point-map-hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X h)
htpy-map-ℤ-Pointed-Type-With-Aut X h (inr (inr zero-ℕ)) =
  ( ap
    ( map-aut-Pointed-Type-With-Aut X)
    ( htpy-map-ℤ-Pointed-Type-With-Aut X h (inr (inl star)))) ∙
  ( inv
    ( preserves-aut-map-hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut
      X h (inr (inl star))))
htpy-map-ℤ-Pointed-Type-With-Aut X h (inr (inr (succ-ℕ k))) =
  ( ap
    ( map-aut-Pointed-Type-With-Aut X)
    ( htpy-map-ℤ-Pointed-Type-With-Aut X h (inr (inr k)))) ∙
  ( inv
    ( preserves-aut-map-hom-Pointed-Type-With-Aut
      ℤ-Pointed-Type-With-Aut X h (inr (inr k))))

coh-point-htpy-map-ℤ-Pointed-Type-With-Aut :
  {l : Level} (X : Pointed-Type-With-Aut l)
  (h : hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X) →
  ( preserves-point-map-ℤ-Pointed-Type-With-Aut X) ＝
  ( ( htpy-map-ℤ-Pointed-Type-With-Aut X h zero-ℤ) ∙
    ( preserves-point-map-hom-Pointed-Type-With-Aut
      ℤ-Pointed-Type-With-Aut X h))
coh-point-htpy-map-ℤ-Pointed-Type-With-Aut X h =
  inv
    ( left-inv
      ( preserves-point-map-hom-Pointed-Type-With-Aut
        ℤ-Pointed-Type-With-Aut X h))

coh-aut-htpy-map-ℤ-Pointed-Type-With-Aut :
  {l : Level} (X : Pointed-Type-With-Aut l)
  (h : hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X)
  (k : ℤ) →
  ( ( preserves-aut-map-ℤ-Pointed-Type-With-Aut X k) ∙
    ( ap
      ( map-aut-Pointed-Type-With-Aut X)
      ( htpy-map-ℤ-Pointed-Type-With-Aut X h k))) ＝
  ( ( htpy-map-ℤ-Pointed-Type-With-Aut X h (succ-ℤ k)) ∙
    ( preserves-aut-map-hom-Pointed-Type-With-Aut
      ℤ-Pointed-Type-With-Aut X h k))
coh-aut-htpy-map-ℤ-Pointed-Type-With-Aut X h (inl zero-ℕ) =
  inv
    ( left-transpose-eq-concat
      ( is-section-map-inv-equiv
        ( aut-Pointed-Type-With-Aut X)
        ( point-Pointed-Type-With-Aut X))
      ( ( htpy-map-ℤ-Pointed-Type-With-Aut X h zero-ℤ) ∙
        ( preserves-aut-map-hom-Pointed-Type-With-Aut
          ℤ-Pointed-Type-With-Aut X h neg-one-ℤ))
      ( ap
        ( map-equiv (aut-Pointed-Type-With-Aut X))
        ( htpy-map-ℤ-Pointed-Type-With-Aut X h neg-one-ℤ))
      ( triangle-eq-transpose-equiv-inv
        ( aut-Pointed-Type-With-Aut X)
        ( ( inv
            ( preserves-point-map-hom-Pointed-Type-With-Aut
              ℤ-Pointed-Type-With-Aut X h)) ∙
          ( preserves-aut-map-hom-Pointed-Type-With-Aut
            ℤ-Pointed-Type-With-Aut X h neg-one-ℤ))))
coh-aut-htpy-map-ℤ-Pointed-Type-With-Aut X h (inl (succ-ℕ k)) =
  inv
    ( left-transpose-eq-concat
      ( is-section-map-inv-equiv
        ( aut-Pointed-Type-With-Aut X)
        ( map-ℤ-Pointed-Type-With-Aut X (inl k)))
      ( ( htpy-map-ℤ-Pointed-Type-With-Aut X h (inl k)) ∙
        ( preserves-aut-map-hom-Pointed-Type-With-Aut
          ℤ-Pointed-Type-With-Aut X h (inl (succ-ℕ k))))
      ( ap
        ( map-equiv (aut-Pointed-Type-With-Aut X))
        ( htpy-map-ℤ-Pointed-Type-With-Aut X h (inl (succ-ℕ k))))
      ( triangle-eq-transpose-equiv-inv
        ( aut-Pointed-Type-With-Aut X)
        ( ( htpy-map-ℤ-Pointed-Type-With-Aut X h (inl k)) ∙
          ( preserves-aut-map-hom-Pointed-Type-With-Aut
            ℤ-Pointed-Type-With-Aut X h (inl (succ-ℕ k))))))
coh-aut-htpy-map-ℤ-Pointed-Type-With-Aut X h (inr (inl star)) =
  ( inv right-unit) ∙
  ( ( ap
      ( concat
        ( ap
          ( map-aut-Pointed-Type-With-Aut X)
          ( htpy-map-ℤ-Pointed-Type-With-Aut X h zero-ℤ))
        ( map-aut-Pointed-Type-With-Aut X
          ( map-hom-Pointed-Type-With-Aut
            ℤ-Pointed-Type-With-Aut X h zero-ℤ)))
      ( inv (left-inv
        ( preserves-aut-map-hom-Pointed-Type-With-Aut
          ℤ-Pointed-Type-With-Aut X h zero-ℤ)))) ∙
    ( inv
      ( assoc
        ( ap
          ( map-aut-Pointed-Type-With-Aut X)
          ( htpy-map-ℤ-Pointed-Type-With-Aut X h zero-ℤ))
        ( inv
          ( preserves-aut-map-hom-Pointed-Type-With-Aut
            ℤ-Pointed-Type-With-Aut X h zero-ℤ))
        ( preserves-aut-map-hom-Pointed-Type-With-Aut
          ℤ-Pointed-Type-With-Aut X h zero-ℤ))))
coh-aut-htpy-map-ℤ-Pointed-Type-With-Aut X h (inr (inr zero-ℕ)) =
  ( inv right-unit) ∙
  ( ( ap
      ( concat
        ( ap
          ( map-aut-Pointed-Type-With-Aut X)
          ( htpy-map-ℤ-Pointed-Type-With-Aut X h one-ℤ))
        ( map-aut-Pointed-Type-With-Aut X
          ( map-hom-Pointed-Type-With-Aut
            ℤ-Pointed-Type-With-Aut X h one-ℤ)))
      ( inv (left-inv
        ( preserves-aut-map-hom-Pointed-Type-With-Aut
          ℤ-Pointed-Type-With-Aut X h one-ℤ)))) ∙
    ( inv
      ( assoc
        ( ap
          ( map-aut-Pointed-Type-With-Aut X)
          ( htpy-map-ℤ-Pointed-Type-With-Aut X h one-ℤ))
        ( inv
          ( preserves-aut-map-hom-Pointed-Type-With-Aut
            ℤ-Pointed-Type-With-Aut X h one-ℤ))
        ( preserves-aut-map-hom-Pointed-Type-With-Aut
          ℤ-Pointed-Type-With-Aut X h one-ℤ))))
coh-aut-htpy-map-ℤ-Pointed-Type-With-Aut X h (inr (inr (succ-ℕ k))) =
  ( inv right-unit) ∙
  ( ( ap
      ( concat
        ( ap
          ( map-aut-Pointed-Type-With-Aut X)
          ( htpy-map-ℤ-Pointed-Type-With-Aut X h (inr (inr (succ-ℕ k)))))
        ( map-aut-Pointed-Type-With-Aut X
          ( map-hom-Pointed-Type-With-Aut
            ℤ-Pointed-Type-With-Aut X h (inr (inr (succ-ℕ k))))))
      ( inv (left-inv
        ( preserves-aut-map-hom-Pointed-Type-With-Aut
          ℤ-Pointed-Type-With-Aut X h (inr (inr (succ-ℕ k))))))) ∙
    ( inv
      ( assoc
        ( ap
          ( map-aut-Pointed-Type-With-Aut X)
          ( htpy-map-ℤ-Pointed-Type-With-Aut X h (inr (inr (succ-ℕ k)))))
        ( inv
          ( preserves-aut-map-hom-Pointed-Type-With-Aut
            ℤ-Pointed-Type-With-Aut X h (inr (inr (succ-ℕ k)))))
        ( preserves-aut-map-hom-Pointed-Type-With-Aut
          ℤ-Pointed-Type-With-Aut X h (inr (inr (succ-ℕ k)))))))

htpy-hom-ℤ-Pointed-Type-With-Aut :
  {l : Level} (X : Pointed-Type-With-Aut l) →
  (h : hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X) →
  htpy-hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X
    (hom-ℤ-Pointed-Type-With-Aut X) h
htpy-hom-ℤ-Pointed-Type-With-Aut X h =
  pair
    ( htpy-map-ℤ-Pointed-Type-With-Aut X h)
    ( pair
      ( coh-point-htpy-map-ℤ-Pointed-Type-With-Aut X h)
      ( coh-aut-htpy-map-ℤ-Pointed-Type-With-Aut X h))

is-initial-ℤ-Pointed-Type-With-Aut :
  {l : Level} (X : Pointed-Type-With-Aut l) →
  is-contr (hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X)
is-initial-ℤ-Pointed-Type-With-Aut X =
  pair
    ( hom-ℤ-Pointed-Type-With-Aut X)
    ( λ h →
      eq-htpy-hom-Pointed-Type-With-Aut ℤ-Pointed-Type-With-Aut X
        ( hom-ℤ-Pointed-Type-With-Aut X)
        ( h)
        ( htpy-hom-ℤ-Pointed-Type-With-Aut X h))
```
