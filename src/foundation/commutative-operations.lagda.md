---
title: Commutative operations
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.commutative-operations where

open import foundation.coproduct-types using (_+_; inl; inr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( map-equiv; _≃_; htpy-equiv; _∘e_; inv-equiv; id-equiv)
open import foundation.function-extensionality using (htpy-eq)
open import foundation.functions using (_∘_)
open import foundation.functoriality-coproduct-types using (map-equiv-coprod)
open import foundation.identity-types using (_＝_; ap-binary; ap; _∙_)
open import foundation.mere-equivalences using (refl-mere-equiv)
open import foundation.sets using (UU-Set; type-Set)
open import
  foundation.universal-property-propositional-truncation-into-sets using
  ( map-universal-property-set-quotient-trunc-Prop;
    htpy-universal-property-set-quotient-trunc-Prop)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_; lzero)
open import foundation.unordered-pairs using
  ( unordered-pair; standard-unordered-pair;
    is-commutative-standard-unordered-pair)

open import univalent-combinatorics.2-element-types using
  ( decide-value-equiv-Fin-two-ℕ; equiv-ev-zero-htpy-equiv-Fin-two-ℕ)
open import univalent-combinatorics.finite-types using (Fin-UU-Fin)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; zero-Fin; one-Fin; equiv-succ-Fin)
```

## Idea

Recall that there is a standard unordered pairing operation `{-,-} : A → (A → unordered-pair A)`. This induces for any type `B` a map

```md
  λ f x y → f {x,y} : (unordered-pair A → B) → (A → A → B)
```

A binary operation `μ : A → A → B` is (coherently) commutative if it extends to an operation `μ̃ : unordered-pair A → B` along `{-,-}`. That is, a binary operation `μ` is commutative if there is an operation `μ̃` on the undordered pairs in `A`, such that `μ̃({x,y}) = μ(x,y)` for all `x, y : A`. One can check that if `B` is a set, then `μ` has such an extension if and only if it is commutative in the usual algebraic sense. Thus we simply say that a commutative operation from `A` to `B` is a map from the unordered pairs in `A` into `B`.

## Definition

### The (incoherent) algebraic condition of commutativity

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where
  
  is-commutative : (A → A → B) → UU (l1 ⊔ l2)
  is-commutative f = (x y : A) → f x y ＝ f y x
```

### Commutative operations

```agda
commutative-operation :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (lsuc lzero ⊔ l1 ⊔ l2)
commutative-operation A B = unordered-pair A → B
```

## Properties

### The restriction of a commutative operation to the standard unordered pairs is commutative

```agda
is-commutative-commutative-operation :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : commutative-operation A B) →
  is-commutative (λ x y → f (standard-unordered-pair x y))
is-commutative-commutative-operation f x y =
  ap f (is-commutative-standard-unordered-pair x y)
```

### A binary operation from $A$ to $B$ is commutative if and only if it extends to the unordered pairs in $A$.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2)
  where

  is-weakly-constant-on-equivalences-is-commutative :
    (f : A → A → type-Set B) (H : is-commutative f) →
    (X : UU lzero) (p : X → A) (e e' : Fin 2 ≃ X) →
    (htpy-equiv e e') + (htpy-equiv e (e' ∘e equiv-succ-Fin 2)) →
    ( f (p (map-equiv e (zero-Fin 1))) (p (map-equiv e (one-Fin 1)))) ＝ 
    ( f (p (map-equiv e' (zero-Fin 1))) (p (map-equiv e' (one-Fin 1))))
  is-weakly-constant-on-equivalences-is-commutative f H X p e e' (inl K) =
    ap-binary f (ap p (K (zero-Fin 1))) (ap p (K (one-Fin 1)))
  is-weakly-constant-on-equivalences-is-commutative f H X p e e' (inr K) =
    ( ap-binary f (ap p (K (zero-Fin 1))) (ap p (K (one-Fin 1)))) ∙
    ( H (p (map-equiv e' (one-Fin 1))) (p (map-equiv e' (zero-Fin 1))))
  
  commutative-operation-is-commutative :
    (f : A → A → type-Set B) → is-commutative f →
    commutative-operation A (type-Set B)
  commutative-operation-is-commutative f H (pair (pair X K) p) =
    map-universal-property-set-quotient-trunc-Prop B
      ( λ e → f (p (map-equiv e (zero-Fin 1))) (p (map-equiv e (one-Fin 1))))
      ( λ e e' →
        is-weakly-constant-on-equivalences-is-commutative f H X p e e'
          ( map-equiv-coprod
            ( inv-equiv (equiv-ev-zero-htpy-equiv-Fin-two-ℕ (pair X K) e e'))
            ( inv-equiv (equiv-ev-zero-htpy-equiv-Fin-two-ℕ
              ( pair X K)
              ( e)
              ( e' ∘e equiv-succ-Fin 2)))
            ( decide-value-equiv-Fin-two-ℕ
              ( pair X K)
              ( e')
              ( map-equiv e (zero-Fin 1)))))
      ( K)

  compute-commutative-operation-is-commutative :
    (f : A → A → type-Set B) (H : is-commutative f) (x y : A) →
    commutative-operation-is-commutative f H (standard-unordered-pair x y) ＝
    f x y
  compute-commutative-operation-is-commutative f H x y =
    
    htpy-universal-property-set-quotient-trunc-Prop B
      ( λ e → f (p (map-equiv e (zero-Fin 1))) (p (map-equiv e (one-Fin 1))))
      ( λ e e' →
        is-weakly-constant-on-equivalences-is-commutative f H (Fin 2) p e e'
          ( map-equiv-coprod
            ( inv-equiv
              ( equiv-ev-zero-htpy-equiv-Fin-two-ℕ (Fin-UU-Fin 2) e e'))
            ( inv-equiv (equiv-ev-zero-htpy-equiv-Fin-two-ℕ
              ( Fin-UU-Fin 2)
              ( e)
              ( e' ∘e equiv-succ-Fin 2)))
            ( decide-value-equiv-Fin-two-ℕ
              ( Fin-UU-Fin 2)
              ( e')
              ( map-equiv e (zero-Fin 1)))))
      ( id-equiv)
    where
    p : Fin 2 → A
    p = pr2 (standard-unordered-pair x y)
```
