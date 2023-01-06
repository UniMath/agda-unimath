---
title: dependent-paths
---
description: some of the path algebra of dependent paths

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.dependent-paths where

open import foundation.identity-types
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.universe-levels
```

Define concatination and inverses of dependent paths

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 a2 : A} {p01 : a0 ＝ a1} {p12 : a1 ＝ a2} {B : A → UU l2} {b0 : B a0} {b1 : B a1} {b2 : B a2}
  (q01 : path-over B p01 b0 b1) (q12 : path-over B p12 b1 b2)
  where

  d-concat : path-over B (p01 ∙ p12) b0 b2
  d-concat = (tr-concat p01 p12 b0) ∙ ((ap (tr B p12) q01) ∙ (q12))

  d-inv : path-over B (inv p01) b1 b0
  d-inv = (inv (ap (tr B (inv p01)) q01)) ∙ ((inv (tr-concat (p01) (inv p01) b0)) ∙ (ap (λ t → tr B t b0) (right-inv p01)))
```

Now we prove these paths satisfy identities analgous to the usual unit, inverse, and associativity laws. Though, due to the dependent nature, these identities are more complicated.

```agda

```
