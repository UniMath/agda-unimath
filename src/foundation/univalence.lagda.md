---
title: The univalence axiom
---

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
open import foundation-core.identity-types using (_＝_; refl; _∙_; inv; ap)
open import foundation-core.universe-levels using (Level; UU; _⊔_)

open import foundation.equality-dependent-function-types using
  ( is-contr-total-Eq-Π)
open import foundation.equivalences using
  ( _≃_; map-inv-is-equiv; id-equiv; is-equiv; _∘e_;
    eq-htpy-equiv; map-equiv; right-inverse-law-equiv; inv-equiv)
open import foundation.injective-maps using (is-injective-map-equiv)
```

## Idea

The univalence axiom characterizes the identity types of universes. It asserts that the map `Id A B → A ≃ B` is an equivalence.

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
  {l1 l2 : Level} {A : UU l1} (B C : A → UU l2) → B ＝ C → equiv-fam B C
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

extensionality-fam :
  {l1 l2 : Level} {A : UU l1} (B C : A → UU l2) → (B ＝ C) ≃ equiv-fam B C
pr1 (extensionality-fam B C) = equiv-eq-fam B C
pr2 (extensionality-fam B C) = is-equiv-equiv-eq-fam B C

eq-equiv-fam :
  {l1 l2 : Level} {A : UU l1} {B C : A → UU l2} → equiv-fam B C → B ＝ C
eq-equiv-fam {B = B} {C} = map-inv-is-equiv (is-equiv-equiv-eq-fam B C)
```

```agda
comp-equiv-eq : {l : Level} {A B C : UU l} (p : A ＝ B) (q : B ＝ C) →
  ((equiv-eq q) ∘e (equiv-eq p)) ＝ equiv-eq (p ∙ q)
comp-equiv-eq refl refl = eq-htpy-equiv refl-htpy

comp-eq-equiv : {l : Level} (A B C : UU l) (f : A ≃ B) (g : B ≃ C) →
  ((eq-equiv A B f) ∙ (eq-equiv B C g)) ＝ eq-equiv A C (g ∘e f)
comp-eq-equiv A B C f g =
  is-injective-map-equiv
    ( equiv-univalence)
    ( ( inv ( comp-equiv-eq (eq-equiv A B f) (eq-equiv B C g))) ∙
      ( ( ap
        ( λ e → (map-equiv e g) ∘e (equiv-eq (eq-equiv A B f)))
        ( right-inverse-law-equiv equiv-univalence)) ∙
        ( ( ap (λ e → g ∘e map-equiv e f) (right-inverse-law-equiv equiv-univalence)) ∙
          ( ap (λ e → map-equiv e (g ∘e f)) (inv (right-inverse-law-equiv equiv-univalence))))))

commutativity-inv-equiv-eq : {l : Level} (A B : UU l) (p : A ＝ B) →
  inv-equiv (equiv-eq p) ＝ equiv-eq (inv p)
commutativity-inv-equiv-eq A .A refl = eq-htpy-equiv refl-htpy

commutativity-inv-eq-equiv : {l : Level} (A B : UU l) (f : A ≃ B) →
  inv (eq-equiv A B f) ＝ eq-equiv B A (inv-equiv f)
commutativity-inv-eq-equiv A B f =
  is-injective-map-equiv
    ( equiv-univalence)
    ( ( inv (commutativity-inv-equiv-eq A B (eq-equiv A B f))) ∙
      ( ( ap
        ( λ e → (inv-equiv (map-equiv e f)))
        ( right-inverse-law-equiv equiv-univalence)) ∙
        ( ap
          ( λ e → map-equiv e (inv-equiv f))
          ( inv (right-inverse-law-equiv equiv-univalence)))))
```
