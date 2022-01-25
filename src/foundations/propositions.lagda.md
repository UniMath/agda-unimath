---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.propositions where

open import foundations.contractible-types using
  ( is-contr; eq-is-contr; is-contr-unit; is-equiv-is-contr; is-contr-is-equiv)
open import foundations.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundations.embeddings using (is-emb; is-emb-is-equiv)
open import foundations.empty-type using (empty)
open import foundations.equivalences using
  ( is-equiv; _≃_; is-equiv-has-inverse; is-equiv-map-inv-is-equiv)
open import foundations.functions using (_∘_)
open import foundations.identity-types using (Id; refl; left-inv; inv; _∙_; ap)
open import foundations.levels using (Level; UU; lsuc; lzero)
open import foundations.unit-type using (unit; star; terminal-map)
```

# Propositions

```agda
is-prop :
  {i : Level} (A : UU i) → UU i
is-prop A = (x y : A) → is-contr (Id x y)

UU-Prop :
  (l : Level) → UU (lsuc l)
UU-Prop l = Σ (UU l) is-prop

module _
  {l : Level}
  where

  type-Prop : UU-Prop l → UU l
  type-Prop P = pr1 P

  abstract
    is-prop-type-Prop : (P : UU-Prop l) → is-prop (type-Prop P)
    is-prop-type-Prop P = pr2 P

module _
  {l : Level} {A : UU l}
  where
  
  contraction-is-prop-is-contr :
    (H : is-contr A) {x y : A} (p : Id x y) → Id (eq-is-contr H) p
  contraction-is-prop-is-contr (pair c C) {x} refl = left-inv (C x)

  abstract
    is-prop-is-contr : is-contr A → is-prop A
    pr1 (is-prop-is-contr H x y) = eq-is-contr H
    pr2 (is-prop-is-contr H x y) = contraction-is-prop-is-contr H

abstract
  is-prop-unit : is-prop unit
  is-prop-unit = is-prop-is-contr is-contr-unit

unit-Prop : UU-Prop lzero
pr1 unit-Prop = unit
pr2 unit-Prop = is-prop-unit

abstract
  is-prop-empty : is-prop empty
  is-prop-empty ()

empty-Prop : UU-Prop lzero
pr1 empty-Prop = empty
pr2 empty-Prop = is-prop-empty
```

## Equivalent characterizations of propositions

```agda
module _
  {l : Level} (A : UU l)
  where
  
  all-elements-equal : UU l
  all-elements-equal = (x y : A) → Id x y
  
  is-proof-irrelevant : UU l
  is-proof-irrelevant = A → is-contr A
  
  is-subterminal : UU l
  is-subterminal = is-emb (terminal-map {A = A})

module _
  {l : Level} {A : UU l}
  where
  
  abstract
    is-prop-all-elements-equal : all-elements-equal A → is-prop A
    pr1 (is-prop-all-elements-equal H x y) = (inv (H x x)) ∙ (H x y)
    pr2 (is-prop-all-elements-equal H x .x) refl = left-inv (H x x)

  abstract
    eq-is-prop' : is-prop A → all-elements-equal A
    eq-is-prop' H x y = pr1 (H x y)

  abstract
    eq-is-prop : is-prop A → {x y : A} → Id x y
    eq-is-prop H {x} {y} = eq-is-prop' H x y

  abstract
    is-proof-irrelevant-all-elements-equal :
      all-elements-equal A → is-proof-irrelevant A
    pr1 (is-proof-irrelevant-all-elements-equal H a) = a
    pr2 (is-proof-irrelevant-all-elements-equal H a) = H a

  abstract
    is-proof-irrelevant-is-prop : is-prop A → is-proof-irrelevant A
    is-proof-irrelevant-is-prop =
      is-proof-irrelevant-all-elements-equal ∘ eq-is-prop'

  abstract
    is-prop-is-proof-irrelevant : is-proof-irrelevant A → is-prop A
    is-prop-is-proof-irrelevant H x y = is-prop-is-contr (H x) x y

  abstract
    eq-is-proof-irrelevant : is-proof-irrelevant A → all-elements-equal A
    eq-is-proof-irrelevant H = eq-is-prop' (is-prop-is-proof-irrelevant H)

  abstract
    is-emb-is-emb :
      {l2 : Level} {B : UU l2} {f : A → B} → (A → is-emb f) → is-emb f
    is-emb-is-emb H x y = H x x y

  abstract
    is-subterminal-is-proof-irrelevant :
      is-proof-irrelevant A → is-subterminal A
    is-subterminal-is-proof-irrelevant H =
      is-emb-is-emb
        ( λ x → is-emb-is-equiv (is-equiv-is-contr _ (H x) is-contr-unit))

  abstract
    is-subterminal-all-elements-equal : all-elements-equal A → is-subterminal A
    is-subterminal-all-elements-equal =
      is-subterminal-is-proof-irrelevant ∘
      is-proof-irrelevant-all-elements-equal

  abstract
    is-subterminal-is-prop : is-prop A → is-subterminal A
    is-subterminal-is-prop = is-subterminal-all-elements-equal ∘ eq-is-prop'

  abstract
    is-prop-is-subterminal : is-subterminal A → is-prop A
    is-prop-is-subterminal H x y =
      is-contr-is-equiv
        ( Id star star)
        ( ap terminal-map)
        ( H x y)
        ( is-prop-is-contr is-contr-unit star star)

  abstract
    eq-is-subterminal : is-subterminal A → all-elements-equal A
    eq-is-subterminal = eq-is-prop' ∘ is-prop-is-subterminal

  abstract
    is-proof-irrelevant-is-subterminal :
      is-subterminal A → is-proof-irrelevant A
    is-proof-irrelevant-is-subterminal H =
      is-proof-irrelevant-all-elements-equal (eq-is-subterminal H)
```

## A map between propositions is an equivalence if there is a map in the reverse direction

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-equiv-is-prop :
      is-prop A → is-prop B → {f : A → B} → (B → A) → is-equiv f
    is-equiv-is-prop is-prop-A is-prop-B {f} g =
      is-equiv-has-inverse
        ( g)
        ( λ y → eq-is-prop is-prop-B)
        ( λ x → eq-is-prop is-prop-A)

  abstract
    equiv-prop : is-prop A → is-prop B → (A → B) → (B → A) → A ≃ B
    pr1 (equiv-prop is-prop-A is-prop-B f g) = f
    pr2 (equiv-prop is-prop-A is-prop-B f g) =
      is-equiv-is-prop is-prop-A is-prop-B g
```

## Propositions are closed under equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-prop-is-equiv : {f : A → B} → is-equiv f → is-prop B → is-prop A
    is-prop-is-equiv {f} E H x y =
      is-contr-is-equiv _ (ap f {x} {y}) (is-emb-is-equiv E x y) (H (f x) (f y))

  abstract
    is-prop-equiv : A ≃ B → is-prop B → is-prop A
    is-prop-equiv (pair f is-equiv-f) = is-prop-is-equiv is-equiv-f

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-prop-is-equiv' : {f : A → B} → is-equiv f → is-prop A → is-prop B
    is-prop-is-equiv' E H =
      is-prop-is-equiv (is-equiv-map-inv-is-equiv E) H

  abstract
    is-prop-equiv' : A ≃ B → is-prop A → is-prop B
    is-prop-equiv' (pair f is-equiv-f) = is-prop-is-equiv' is-equiv-f
```
