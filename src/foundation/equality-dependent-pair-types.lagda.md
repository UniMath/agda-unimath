# Equality of dependent pair types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.equality-dependent-pair-types where

open import foundation.identity-types using
  (Id; refl; tr; _∙_; concat; ap; tr-concat; inv; isretr-inv-tr)

open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.equivalences using
  ( is-equiv; _≃_; is-equiv-has-inverse)
open import foundation-core.functions using (id; _∘_)
open import foundation-core.homotopies using (_~_)
open import foundation-core.propositions using (is-prop; eq-is-prop)
open import foundation-core.universe-levels using (UU; Level; _⊔_)
```

## Idea

An identification `Id (pair x y) (pair x' y')` in a dependent pair type `Σ A B` is equivalently described as a pair `pair α β` consisting of an identification `α : Id x x'` and an identification `β : Id (tr B α y) y'`. 

## Definition

```agda

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  Eq-Σ : (s t : Σ A B) → UU (l1 ⊔ l2)
  Eq-Σ s t = Σ (Id (pr1 s) (pr1 t)) (λ α → Id (tr B α (pr2 s)) (pr2 t))
```

## Properties

### The type `Id s t` is equivalent to `Eq-Σ s t` for any `s t : Σ A B`.

```agda
  refl-Eq-Σ : (s : Σ A B) → Eq-Σ s s
  pr1 (refl-Eq-Σ (pair a b)) = refl
  pr2 (refl-Eq-Σ (pair a b)) = refl

  pair-eq-Σ : {s t : Σ A B} → Id s t → Eq-Σ s t
  pair-eq-Σ {s} refl = refl-Eq-Σ s

  eq-pair-Σ :
    {s t : Σ A B} →
    (α : Id (pr1 s) (pr1 t)) → Id (tr B α (pr2 s)) (pr2 t) → Id s t
  eq-pair-Σ {pair x y} {pair .x .y} refl refl = refl

  eq-pair-Σ' : {s t : Σ A B} → Eq-Σ s t → Id s t
  eq-pair-Σ' (pair α β) = eq-pair-Σ α β

  isretr-pair-eq-Σ :
    (s t : Σ A B) →
    ((pair-eq-Σ {s} {t}) ∘ (eq-pair-Σ' {s} {t})) ~ id {A = Eq-Σ s t}
  isretr-pair-eq-Σ (pair x y) (pair .x .y) (pair refl refl) = refl

  issec-pair-eq-Σ :
    (s t : Σ A B) → ((eq-pair-Σ' {s} {t}) ∘ (pair-eq-Σ {s} {t})) ~ id
  issec-pair-eq-Σ (pair x y) .(pair x y) refl = refl

  abstract
    is-equiv-eq-pair-Σ : (s t : Σ A B) → is-equiv (eq-pair-Σ' {s} {t})
    is-equiv-eq-pair-Σ s t =
      is-equiv-has-inverse
        ( pair-eq-Σ)
        ( issec-pair-eq-Σ s t)
        ( isretr-pair-eq-Σ s t)

  equiv-eq-pair-Σ : (s t : Σ A B) → Eq-Σ s t ≃ Id s t
  equiv-eq-pair-Σ s t = pair eq-pair-Σ' (is-equiv-eq-pair-Σ s t)

  abstract
    is-equiv-pair-eq-Σ : (s t : Σ A B) → is-equiv (pair-eq-Σ {s} {t})
    is-equiv-pair-eq-Σ s t =
      is-equiv-has-inverse
        ( eq-pair-Σ')
        ( isretr-pair-eq-Σ s t)
        ( issec-pair-eq-Σ s t)

  equiv-pair-eq-Σ : (s t : Σ A B) → Id s t ≃ Eq-Σ s t
  equiv-pair-eq-Σ s t = pair pair-eq-Σ (is-equiv-pair-eq-Σ s t)

  η-pair : (t : Σ A B) → Id (pair (pr1 t) (pr2 t)) t
  η-pair t = eq-pair-Σ refl refl

  comp-eq-pair-Σ :
    {x y z : A} (a : B x) (b : B y) (c : B z) (p : Id x y) (q : Id y z) →
    ( r : Id (tr B p a) b) (s : Id (tr B q b) c) → 
    Id
      ( concat
        {x = pair x a}
        {y = pair y b}
        ( eq-pair-Σ p r)
        ( pair z c)
        ( eq-pair-Σ q s))
      ( eq-pair-Σ (p ∙ q) (tr-concat {B = B} p q a ∙ (ap (tr B q) r ∙ s)))
  comp-eq-pair-Σ a .a .a refl refl refl refl = refl

  comp-pair-eq-Σ : {s t u : Σ A B} (p : Id s t) (q : Id t u) →
    Id (pr1 (pair-eq-Σ p) ∙ pr1 (pair-eq-Σ q)) (pr1 (pair-eq-Σ (p ∙ q)))
  comp-pair-eq-Σ refl refl = refl

  ap-pair-eq-Σ : {l3 : Level} (X : UU l3) (f : X → Σ A B)
    (x y : X) (p : Id x y) →
    Id (pr1 (pair-eq-Σ (ap f p))) (ap (λ x → pr1 (f x)) p)
  ap-pair-eq-Σ X f x .x refl = refl

  inv-eq-pair-Σ : 
    {x y : A} (a : B x) (b : B y) (p : Id x y) (r : Id (tr B p a) b) → 
    Id
      ( inv (eq-pair-Σ p r))
      ( eq-pair-Σ
        ( inv p)
        ( tr
          ( λ x → Id (tr B (inv p) b) x)
          ( isretr-inv-tr B p a)
          ( ap (tr B (inv p)) (inv r))))
  inv-eq-pair-Σ a .a refl refl = refl
```
