---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.finite-presentations where

open import univalent-foundations public

{-------------------------------------------------------------------------------

  Finitely presented types are types A equipped with a map f : Fin k → A such
  that the composite

    Fin k → A → type-trunc-Set A

  is an equivalence.

-------------------------------------------------------------------------------}


```
