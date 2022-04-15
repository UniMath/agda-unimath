# The univalence axiom

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.univalence where

open import foundation-core.univalence public

open import foundation-core.contractible-types using (is-contr; is-contr-equiv)
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.functoriality-dependent-pair-types using
  ( equiv-tot)
open import foundation-core.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation-core.homotopies using (refl-htpy)
open import foundation-core.identity-types using (Id; refl; _∙_; inv; ap)
open import foundation-core.universe-levels using (Level; UU; _⊔_)

open import foundation.equality-dependent-function-types using
  ( is-contr-total-Eq-Π)
open import foundation.equivalences using
  ( _≃_; map-inv-is-equiv; equiv-inv-equiv; id-equiv; is-equiv; _∘e_; eq-htpy-equiv;
    map-equiv; right-inverse-law-equiv)
open import foundation.injective-maps using (is-injective-map-equiv)
```

## Idea

The univalence axiom characterizes the identity types of universes. It asserts that the map `Id A B → A ≃ B` is an equivalence.

## Postulates

```agda
postulate univalence : {i : Level} (A B : UU i) → UNIVALENCE A B
```

## Properties

```agda
eq-equiv : {i : Level} (A B : UU i) → (A ≃ B) → Id A B
eq-equiv A B = map-inv-is-equiv (univalence A B)

equiv-univalence :
  {i : Level} {A B : UU i} → Id A B ≃ (A ≃ B)
pr1 equiv-univalence = equiv-eq
pr2 equiv-univalence = univalence _ _

abstract
  is-contr-total-equiv : {i : Level} (A : UU i) →
    is-contr (Σ (UU i) (λ X → A ≃ X))
  is-contr-total-equiv A = is-contr-total-equiv-UNIVALENCE A (univalence A)

abstract
  is-contr-total-equiv' : {i : Level} (A : UU i) →
    is-contr (Σ (UU i) (λ X → X ≃ A))
  is-contr-total-equiv' A =
    is-contr-equiv
      ( Σ (UU _) (λ X → A ≃ X))
      ( equiv-tot (λ X → equiv-inv-equiv))
      ( is-contr-total-equiv A)
```

### Univalence for type families

```agda
equiv-fam :
  {l1 l2 l3 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3) →
  UU (l1 ⊔ l2 ⊔ l3)
equiv-fam {A = A} B C = (a : A) → B a ≃ C a

id-equiv-fam :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → equiv-fam B B
id-equiv-fam B a = id-equiv

equiv-eq-fam :
  {l1 l2 : Level} {A : UU l1} (B C : A → UU l2) → Id B C → equiv-fam B C
equiv-eq-fam B .B refl = id-equiv-fam B

abstract
  is-contr-total-equiv-fam :
    {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
    is-contr (Σ (A → UU l2) (equiv-fam B))
  is-contr-total-equiv-fam B =
    is-contr-total-Eq-Π
      ( λ x X → (B x) ≃ X)
      ( λ x → is-contr-total-equiv (B x))

abstract
  is-equiv-equiv-eq-fam :
    {l1 l2 : Level} {A : UU l1} (B C : A → UU l2) → is-equiv (equiv-eq-fam B C)
  is-equiv-equiv-eq-fam B =
    fundamental-theorem-id B
      ( id-equiv-fam B)
      ( is-contr-total-equiv-fam B)
      ( equiv-eq-fam B)

eq-equiv-fam :
  {l1 l2 : Level} {A : UU l1} {B C : A → UU l2} → equiv-fam B C → Id B C
eq-equiv-fam {B = B} {C} = map-inv-is-equiv (is-equiv-equiv-eq-fam B C)
```

```agda
comp-equiv-eq : {l : Level} {A B C : UU l} (p : Id A B) (q : Id B C) →
  Id ((equiv-eq q) ∘e (equiv-eq p)) (equiv-eq (p ∙ q)) 
comp-equiv-eq refl refl = eq-htpy-equiv refl-htpy

comp-eq-equiv : {l : Level} (A B C : UU l) (f : A ≃ B) (g : B ≃ C) →
  Id ((eq-equiv A B f) ∙ (eq-equiv B C g)) (eq-equiv A C (g ∘e f))
comp-eq-equiv A B C f g =
  is-injective-map-equiv
    ( equiv-univalence)
    ( ( inv ( comp-equiv-eq (eq-equiv A B f) (eq-equiv B C g))) ∙
      ( ( ap
        ( λ e → (map-equiv e g) ∘e (equiv-eq (eq-equiv A B f)))
        ( right-inverse-law-equiv equiv-univalence)) ∙
        ( ( ap (λ e → g ∘e map-equiv e f) (right-inverse-law-equiv equiv-univalence)) ∙
          ( ap (λ e → map-equiv e (g ∘e f)) (inv (right-inverse-law-equiv equiv-univalence))))))
```
