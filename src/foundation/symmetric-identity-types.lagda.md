---
title: The symmetric identity types
---

```agda
module foundation.symmetric-identity-types where

open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.unordered-pairs

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

## Idea

We construct a variant of the identity type equipped with a natural `ℤ/2`-action.

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  symmetric-Id :
    (a : unordered-pair A) → UU l
  symmetric-Id a =
    Σ A (λ x → (i : type-unordered-pair a) → x ＝ element-unordered-pair a i)

  module _
    (a : unordered-pair A)
    where

    Eq-symmetric-Id :
      (p q : symmetric-Id a) → UU l
    Eq-symmetric-Id (x , H) q =
      Σ (x ＝ pr1 q) (λ p → (i : type-unordered-pair a) → H i ＝ (p ∙ pr2 q i))

    refl-Eq-symmetric-Id :
      (p : symmetric-Id a) → Eq-symmetric-Id p p
    pr1 (refl-Eq-symmetric-Id (x , H)) = refl
    pr2 (refl-Eq-symmetric-Id (x , H)) i = refl

    is-contr-total-Eq-symmetric-Id :
      (p : symmetric-Id a) → is-contr (Σ (symmetric-Id a) (Eq-symmetric-Id p))
    is-contr-total-Eq-symmetric-Id (x , H) =
      is-contr-total-Eq-structure
        ( λ y K p → (i : type-unordered-pair a) → H i ＝ (p ∙ K i))
        ( is-contr-total-path x)
        ( x , refl)
        ( is-contr-total-htpy H)

    Eq-eq-symmetric-Id :
      (p q : symmetric-Id a) → (p ＝ q) → Eq-symmetric-Id p q
    Eq-eq-symmetric-Id p .p refl = refl-Eq-symmetric-Id p

    is-equiv-Eq-eq-symmetric-Id :
      (p q : symmetric-Id a) → is-equiv (Eq-eq-symmetric-Id p q)
    is-equiv-Eq-eq-symmetric-Id p =
      fundamental-theorem-id
        ( is-contr-total-Eq-symmetric-Id p)
        ( Eq-eq-symmetric-Id p)

    extensionality-symmetric-Id :
      (p q : symmetric-Id a) → (p ＝ q) ≃ Eq-symmetric-Id p q
    pr1 (extensionality-symmetric-Id p q) = Eq-eq-symmetric-Id p q
    pr2 (extensionality-symmetric-Id p q) = is-equiv-Eq-eq-symmetric-Id p q

    eq-Eq-symmetric-Id :
      (p q : symmetric-Id a) → Eq-symmetric-Id p q → p ＝ q
    eq-Eq-symmetric-Id p q = map-inv-equiv (extensionality-symmetric-Id p q)

  module _
    (a b : A)
    where

    map-compute-symmetric-Id :
      symmetric-Id (standard-unordered-pair a b) → a ＝ b
    map-compute-symmetric-Id (x , f) = inv (f (zero-Fin 1)) ∙ f (one-Fin 1)

    map-inv-compute-symmetric-Id :
      a ＝ b → symmetric-Id (standard-unordered-pair a b)
    pr1 (map-inv-compute-symmetric-Id p) = a
    pr2 (map-inv-compute-symmetric-Id p) (inl (inr star)) = refl
    pr2 (map-inv-compute-symmetric-Id p) (inr star) = p

    issec-map-inv-compute-symmetric-Id :
      ( map-compute-symmetric-Id ∘ map-inv-compute-symmetric-Id) ~ id
    issec-map-inv-compute-symmetric-Id refl = refl

    isretr-map-inv-compute-symmetric-Id :
      ( map-inv-compute-symmetric-Id ∘ map-compute-symmetric-Id) ~ id
    isretr-map-inv-compute-symmetric-Id (x , f) =
      eq-Eq-symmetric-Id
        ( standard-unordered-pair a b)
        ( map-inv-compute-symmetric-Id (map-compute-symmetric-Id (x , f)))
        ( x , f)
        ( ( inv (f (zero-Fin 1))) ,
          ( λ { ( inl (inr star)) → inv (left-inv (f (zero-Fin 1))) ;
                ( inr star) → refl}))

    is-equiv-map-compute-symmetric-Id :
      is-equiv (map-compute-symmetric-Id)
    is-equiv-map-compute-symmetric-Id =
      is-equiv-has-inverse
        ( map-inv-compute-symmetric-Id)
        ( issec-map-inv-compute-symmetric-Id)
        ( isretr-map-inv-compute-symmetric-Id)

    compute-symmetric-Id :
      symmetric-Id (standard-unordered-pair a b) ≃ (a ＝ b)
    pr1 (compute-symmetric-Id) = map-compute-symmetric-Id
    pr2 (compute-symmetric-Id) = is-equiv-map-compute-symmetric-Id
```
