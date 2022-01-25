---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.propositions where

open import foundations.contractible-types using
  ( is-contr; eq-is-contr; is-contr-unit)
open import foundations.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundations.empty-type using (empty)
open import foundations.identity-types using (Id; refl; left-inv)
open import foundations.levels using (Level; UU; lsuc; lzero)
open import foundations.unit-type using (unit; star)
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
    is-prop-is-contr :
      is-contr A → (x y : A) → is-contr (Id x y)
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
