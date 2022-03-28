# Commutative operations

```agda
{-# OPTIONS --without-K --exact-split #-}

module synthetic-homotopy-theory.commutative-operations where

open import foundation.universe-levels using (Level; UU; lsuc; _⊔_; lzero)
open import foundation.unordered-pairs using (unordered-pair)
```

## Idea

Recall that there is a standard unordered pairing operation $\{{-},{-}\} : A \to (A \to \mathsf{unordered{-}pair}(A)$. This induces for any type $B$ a map

\begin{equation*}
  (\mathsf{unordered{-}pair}(A) \to B) \stackrel{\{{-},{-}\}^{\ast}}{\longrightarrow} (A \to (A \to B)).
\end{equation*}

A binary operation $\mu : A \to A \to B$ is (coherently) commutative if it extends to an operation $\tilde{\mu} : \mathsf{unordered{-}pair}(A) \to B$ along the map $\{{-},{-}\}^{\ast}$. That is, a binary operation $\mu$ is commutative if there is an operation $\tilde{\mu}$ on the undordered pairs in $A$, such that $\tilde{\mu}(\{x,y\})=\mu(x,y)$ for all $x,y:A$. One can check that if $B$ is a set, then $\mu$ has such an extension if and only if it is commutative in the usual algebraic sense. Thus we simply say that a commutative operation from $A$ to $B$ is a map from the unordered pairs in $A$ into $B$.

## Definition

```agda
commutative-operation :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (lsuc lzero ⊔ l1 ⊔ l2)
commutative-operation A B = unordered-pair A → B
```

