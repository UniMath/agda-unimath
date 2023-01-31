# Functoriality of matrices

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.functoriality-matrices where

open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.functoriality-vectors using
  ( map-vec; map-binary-vec)
open import linear-algebra.matrices using (matrix)
```

## Idea

An map `f : A → B` induces a map `matrix A m n → matrix B m n`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where
  
  map-matrix : {m n : ℕ} → matrix A m n → matrix B m n
  map-matrix = map-vec (map-vec f)
```

### Binar maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C)
  where

  map-binary-matrix :
    {m n : ℕ} → matrix A m n → matrix B m n → matrix C m n
  map-binary-matrix = map-binary-vec (map-binary-vec f)
```

