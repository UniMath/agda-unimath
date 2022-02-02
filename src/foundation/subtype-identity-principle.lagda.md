# The subtype identity principle

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.subtype-identity-principle where

open import foundation.contractible-types using
  ( is-contr; is-contr-equiv)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( is-equiv; _≃_; map-equiv; is-equiv-map-equiv)
open import foundation.functions using (_∘_)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id; fundamental-theorem-id')
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-types using (Id; refl)
open import foundation.propositions using
  ( is-prop; is-proof-irrelevant-is-prop; UU-Prop; type-Prop; is-prop-type-Prop)
open import foundation.type-arithmetic-cartesian-product-types using
  ( equiv-right-swap-Σ)
open import foundation.type-arithmetic-dependent-pair-types using
  ( left-unit-law-Σ-is-contr)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

The subtype identity principle allows us to efficiently characterize the identity type of a subtype, using a characterization of the identity type of the base type.

## Lemma

The following is a general construction that will help us show that the identity type of a subtype agrees with the identity type of the  original type. We already know that the first projection of a family of propositions is an embedding, but the following lemma still has its uses.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    is-contr-total-Eq-subtype :
      {l3 : Level} {P : A → UU l3} →
      is-contr (Σ A B) → ((x : A) → is-prop (P x)) →
      (a : A) (b : B a) (p : P a) →
      is-contr (Σ (Σ A P) (λ t → B (pr1 t)))
    is-contr-total-Eq-subtype {l3} {P}
      is-contr-AB is-subtype-P a b p =
      is-contr-equiv
        ( Σ (Σ A B) (λ t → P (pr1 t)))
        ( equiv-right-swap-Σ)
        ( is-contr-equiv
          ( P a)
          ( left-unit-law-Σ-is-contr
            ( is-contr-AB)
            ( pair a b))
          ( is-proof-irrelevant-is-prop (is-subtype-P a) p))
```

## Theorem

### The subtype identity principle

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {P : A → UU l2}
  (is-prop-P : (x : A) → is-prop (P x)) {Eq-A : A → UU l3}
  {a : A} (p : P a) (refl-A : Eq-A a)
  where

  abstract
    subtype-identity-principle :
      {f : (x : A) → Id a x → Eq-A x}
      (h : (z : (Σ A P)) → Id (pair a p) z → Eq-A (pr1 z)) →
      ((x : A) → is-equiv (f x)) → (z : Σ A P) → is-equiv (h z)
    subtype-identity-principle {f} h H =
      fundamental-theorem-id
        ( pair a p)
        ( refl-A)
        ( is-contr-total-Eq-subtype
          ( fundamental-theorem-id' a refl-A f H)
          ( is-prop-P)
          ( a)
          ( refl-A)
          ( p))
        ( h)

module _
  {l1 l2 l3 : Level} {A : UU l1} (P : A → UU-Prop l2) {Eq-A : A → UU l3}
  {a : A} (p : type-Prop (P a)) (refl-A : Eq-A a)
  where

  map-extensionality-subtype :
    (f : (x : A) → Id a x ≃ Eq-A x) →
    (z : Σ A (type-Prop ∘ P)) → Id (pair a p) z → Eq-A (pr1 z)
  map-extensionality-subtype f .(pair a p) refl = refl-A

  extensionality-subtype :
    (f : (x : A) → Id a x ≃ Eq-A x) →
    (z : Σ A (type-Prop ∘ P)) → Id (pair a p) z ≃ Eq-A (pr1 z)
  pr1 (extensionality-subtype f z) = map-extensionality-subtype f z
  pr2 (extensionality-subtype f z) =
    subtype-identity-principle
      ( λ x → is-prop-type-Prop (P x))
      ( p)
      ( refl-A)
      ( map-extensionality-subtype f)
      ( λ x → is-equiv-map-equiv (f x))
      ( z)
```

### Characterizing the identity type of equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  htpy-equiv : A ≃ B → A ≃ B → UU (l1 ⊔ l2)
  htpy-equiv e e' = (map-equiv e) ~ (map-equiv e')

  refl-htpy-equiv : (e : A ≃ B) → htpy-equiv e e
  refl-htpy-equiv e = refl-htpy

  htpy-eq-equiv : {e e' : A ≃ B} (p : Id e e') → htpy-equiv e e'
  htpy-eq-equiv {e = e} {.e} refl =
    refl-htpy-equiv e

  abstract
    is-contr-total-htpy-equiv :
      (e : A ≃ B) → is-contr (Σ (A ≃ B) (λ e' → htpy-equiv e e'))
    is-contr-total-htpy-equiv (pair f is-equiv-f) =
      is-contr-total-Eq-subtype
        ( is-contr-total-htpy f)
        ( is-subtype-is-equiv)
        ( f)
        ( refl-htpy)
        ( is-equiv-f)

  is-equiv-htpy-eq-equiv :
    (e e' : A ≃ B) → is-equiv (htpy-eq-equiv {e = e} {e'})
  is-equiv-htpy-eq-equiv e =
    fundamental-theorem-id e
      ( refl-htpy-equiv e)
      ( is-contr-total-htpy-equiv e)
      ( λ e' → htpy-eq-equiv {e = e} {e'})

  equiv-htpy-eq-equiv :
    (e e' : A ≃ B) → Id e e' ≃ (htpy-equiv e e')
  pr1 (equiv-htpy-eq-equiv e e') = htpy-eq-equiv
  pr2 (equiv-htpy-eq-equiv e e') = is-equiv-htpy-eq-equiv e e'

  eq-htpy-equiv : {e e' : A ≃ B} → ( htpy-equiv e e') → Id e e'
  eq-htpy-equiv {e = e} {e'} = map-inv-is-equiv (is-equiv-htpy-eq-equiv e e')
```
