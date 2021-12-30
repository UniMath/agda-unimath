---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.unordered-pairs where

open import univalent-foundations public

unordered-pair : {l : Level} (A : UU l) → UU (lsuc lzero ⊔ l)
unordered-pair A = Σ (UU-Fin two-ℕ) (λ X → pr1 X → A)

type-unordered-pair : {l : Level} {A : UU l} → unordered-pair A → UU lzero
type-unordered-pair p = pr1 (pr1 p)

has-two-elements-type-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) →
  mere-equiv (Fin two-ℕ) (type-unordered-pair p)
has-two-elements-type-unordered-pair p = pr2 (pr1 p)

pair-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) →
  type-unordered-pair p → A
pair-unordered-pair p = pr2 p

is-in-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) (a : A) → UU l
is-in-unordered-pair p a = ∃ (λ x → Id (pair-unordered-pair p x) a)

is-selfpairing-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) → UU l
is-selfpairing-unordered-pair p =
  (x y : type-unordered-pair p) →
  type-trunc-Prop (Id (pair-unordered-pair p x) (pair-unordered-pair p y))

module _
  {l1 : Level} {A : UU l1}
  where
  
  Eq-unordered-pair : (p q : unordered-pair A) → UU l1
  Eq-unordered-pair (pair X p) (pair Y q) =
    Σ (equiv-UU-Fin X Y) (λ e → p ~ (q ∘ map-equiv e))

  refl-Eq-unordered-pair : (p : unordered-pair A) → Eq-unordered-pair p p
  pr1 (refl-Eq-unordered-pair (pair X p)) = id-equiv-UU-Fin X
  pr2 (refl-Eq-unordered-pair (pair X p)) = refl-htpy

  Eq-eq-unordered-pair :
    (p q : unordered-pair A) → Id p q → Eq-unordered-pair p q
  Eq-eq-unordered-pair p .p refl = refl-Eq-unordered-pair p

  is-contr-total-Eq-unordered-pair :
    (p : unordered-pair A) →
    is-contr (Σ (unordered-pair A) (Eq-unordered-pair p))
  is-contr-total-Eq-unordered-pair (pair X p) =
    is-contr-total-Eq-structure
      ( λ Y q e → p ~ (q ∘ map-equiv e))
      ( is-contr-total-equiv-UU-Fin X)
      ( pair X (id-equiv-UU-Fin X))
      ( is-contr-total-htpy p)

  is-equiv-Eq-eq-unordered-pair :
    (p q : unordered-pair A) → is-equiv (Eq-eq-unordered-pair p q)
  is-equiv-Eq-eq-unordered-pair p =
    fundamental-theorem-id p
      ( refl-Eq-unordered-pair p)
      ( is-contr-total-Eq-unordered-pair p)
      ( Eq-eq-unordered-pair p)

  extensionality-unordered-pair :
    (p q : unordered-pair A) → Id p q ≃ Eq-unordered-pair p q
  pr1 (extensionality-unordered-pair p q) = Eq-eq-unordered-pair p q
  pr2 (extensionality-unordered-pair p q) = is-equiv-Eq-eq-unordered-pair p q

  eq-Eq-unordered-pair :
    (p q : unordered-pair A) → Eq-unordered-pair p q → Id p q
  eq-Eq-unordered-pair p q =
    map-inv-is-equiv (is-equiv-Eq-eq-unordered-pair p q)


map-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  unordered-pair A → unordered-pair B
pr1 (map-unordered-pair f (pair X p)) = X
pr2 (map-unordered-pair f (pair X p)) = f ∘ p

preserves-comp-map-unordered-pair :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) →
  map-unordered-pair (g ∘ f) ~ (map-unordered-pair g ∘ map-unordered-pair f)
preserves-comp-map-unordered-pair g f = {!!}

unordered-distinct-pair :
  {l : Level} (A : UU l) → UU (lsuc lzero ⊔ l)
unordered-distinct-pair A = Σ (UU-Fin two-ℕ) (λ X → pr1 X ↪ A)
```
