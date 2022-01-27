---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.propositions where

open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using
  ( is-contr; eq-is-contr; is-contr-is-equiv; is-contr-equiv'; is-contr-Σ')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb; is-emb-is-equiv)
open import foundation.equality-dependent-pair-types using
  ( Eq-Σ; equiv-eq-pair-Σ)
open import foundation.equivalences using
  ( is-equiv; _≃_; is-equiv-has-inverse; is-equiv-map-inv-is-equiv)
open import foundation.functions using (_∘_)
open import foundation.identity-types using
  ( Id; refl; left-inv; inv; _∙_; ap; tr)
open import foundation.universe-levels using (Level; UU; lsuc; lzero; _⊔_)
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

### Propositions are closed under dependent pair types

```agda
abstract
  is-prop-Σ : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-prop A → ((x : A) → is-prop (B x)) → is-prop (Σ A B)
  is-prop-Σ H K x y =
    is-contr-equiv'
      ( Eq-Σ x y)
      ( equiv-eq-pair-Σ x y)
      ( is-contr-Σ'
        ( H (pr1 x) (pr1 y))
        ( λ p → K (pr1 y) (tr _ p (pr2 x)) (pr2 y)))

Σ-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : type-Prop P → UU-Prop l2) →
  UU-Prop (l1 ⊔ l2)
pr1 (Σ-Prop P Q) = Σ (type-Prop P) (λ p → type-Prop (Q p))
pr2 (Σ-Prop P Q) =
  is-prop-Σ
    ( is-prop-type-Prop P)
    ( λ p → is-prop-type-Prop (Q p))
```

### Propositions are closed under cartesian product types

```agda
abstract
  is-prop-prod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-prop A → is-prop B → is-prop (A × B)
  is-prop-prod H K = is-prop-Σ H (λ x → K)

prod-Prop : {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
pr1 (prod-Prop P Q) = type-Prop P × type-Prop Q
pr2 (prod-Prop P Q) = is-prop-prod (is-prop-type-Prop P) (is-prop-type-Prop Q)
```
