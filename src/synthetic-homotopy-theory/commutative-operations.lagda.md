# Commutative operations

```agda
{-# OPTIONS --without-K --exact-split #-}

module synthetic-homotopy-theory.commutative-operations where

open import foundation.universe-levels using (Level; UU; lsuc; _⊔_; lzero)
open import foundation.unordered-pairs using (unordered-pair)
```

## Idea

A binary operation $\mu : A \to A \to A$ is (coherently) commutative if it extends to an operation $\tilde{\mu} : \mathsf{unordered{-}pair}(A) → A$. Thus we simply say that a commutative operation on $A$ is a map from the unordered pairs in $A$ into $A$.

## Definition

```agda
commutative-operation :
  {l : Level} (A : UU l) → UU (lsuc lzero ⊔ l)
commutative-operation A = unordered-pair A → A
```
