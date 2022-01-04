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

is-set-type-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) → is-set (type-unordered-pair p)
is-set-type-unordered-pair p =
  is-set-mere-equiv' (has-two-elements-type-unordered-pair p) (is-set-Fin two-ℕ)

has-decidable-equality-type-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) →
  has-decidable-equality (type-unordered-pair p)
has-decidable-equality-type-unordered-pair p =
  has-decidable-equality-mere-equiv'
    ( has-two-elements-type-unordered-pair p)
    ( has-decidable-equality-Fin)

element-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) →
  type-unordered-pair p → A
element-unordered-pair p = pr2 p

{-
module _
  {l : Level} {A : UU l}
  where

  is-injective-map-Fin-two-ℕ :
    (f : Fin two-ℕ → A) →
    ¬ (Id (f zero-Fin) (f one-Fin)) → is-injective f
  is-injective-map-Fin-two-ℕ f H {inl (inr star)} {inl (inr star)} p = refl
  is-injective-map-Fin-two-ℕ f H {inl (inr star)} {inr star} p = ex-falso (H p)
  is-injective-map-Fin-two-ℕ f H {inr star} {inl (inr star)} p =
    ex-falso (H (inv p))
  is-injective-map-Fin-two-ℕ f H {inr star} {inr star} p = refl
  
  is-injective-element-unordered-pair :
    (p : unordered-pair A) →
    ¬ ( (x y : type-unordered-pair p) →
        Id (element-unordered-pair p x) (element-unordered-pair p y)) →
    is-injective (element-unordered-pair p)
  is-injective-element-unordered-pair (pair X f) H {x} = {!!}
    where
    g : Fin two-ℕ → A
    g (inl (inr star)) = {!!}
    g (inr star) = {!!}
  
-}

is-in-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) (a : A) → UU l
is-in-unordered-pair p a = ∃ (λ x → Id (element-unordered-pair p x) a)

is-selfpairing-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) → UU l
is-selfpairing-unordered-pair p =
  (x y : type-unordered-pair p) →
  type-trunc-Prop (Id (element-unordered-pair p x) (element-unordered-pair p y))

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

  isretr-eq-Eq-unordered-pair :
    (p q : unordered-pair A) →
    (eq-Eq-unordered-pair p q ∘ Eq-eq-unordered-pair p q) ~ id
  isretr-eq-Eq-unordered-pair p q =
    isretr-map-inv-is-equiv (is-equiv-Eq-eq-unordered-pair p q)

map-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  unordered-pair A → unordered-pair B
pr1 (map-unordered-pair f (pair X p)) = X
pr2 (map-unordered-pair f (pair X p)) = f ∘ p

preserves-comp-map-unordered-pair :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) →
  map-unordered-pair (g ∘ f) ~ (map-unordered-pair g ∘ map-unordered-pair f)
preserves-comp-map-unordered-pair g f p = refl

preserves-id-map-unordered-pair :
  {l1 : Level} {A : UU l1} →
  map-unordered-pair (id {A = A}) ~ id
preserves-id-map-unordered-pair = refl-htpy

htpy-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
  (f ~ g) → (map-unordered-pair f ~ map-unordered-pair g)
htpy-unordered-pair {f = f} {g = g} H (pair X p) =
  eq-Eq-unordered-pair
    ( map-unordered-pair f (pair X p))
    ( map-unordered-pair g (pair X p))
    ( pair id-equiv (H ·r p))

preserves-refl-htpy-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  htpy-unordered-pair (refl-htpy {f = f}) ~ refl-htpy
preserves-refl-htpy-unordered-pair f p =
  isretr-eq-Eq-unordered-pair
    ( map-unordered-pair f p)
    ( map-unordered-pair f p)
    ( refl)

equiv-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (unordered-pair A ≃ unordered-pair B)
equiv-unordered-pair e = equiv-tot (λ X → equiv-postcomp (type-UU-Fin X) e)

map-equiv-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (unordered-pair A → unordered-pair B)
map-equiv-unordered-pair e = map-equiv (equiv-unordered-pair e)

is-equiv-map-equiv-unordered-pair :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (e : A ≃ B) → is-equiv (map-equiv-unordered-pair e)
is-equiv-map-equiv-unordered-pair e =
  is-equiv-map-equiv (equiv-unordered-pair e)

unordered-distinct-pair :
  {l : Level} (A : UU l) → UU (lsuc lzero ⊔ l)
unordered-distinct-pair A = Σ (UU-Fin two-ℕ) (λ X → pr1 X ↪ A)
```
