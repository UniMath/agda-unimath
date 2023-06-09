# Symmetric operations

```agda
module foundation.symmetric-operations where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.functoriality-coproduct-types
open import foundation.universal-property-propositional-truncation-into-sets
open import foundation.universe-levels
open import foundation.unordered-pairs

open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.sets

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Recall that there is a standard unordered pairing operation
`{-,-} : A → (A → unordered-pair A)`. This induces for any type `B` a map

```text
  λ f x y → f {x,y} : (unordered-pair A → B) → (A → A → B)
```

A binary operation `μ : A → A → B` is symmetric if it extends to an operation
`μ̃ : unordered-pair A → B` along `{-,-}`. That is, a binary operation `μ` is
symmetric if there is an operation `μ̃` on the undordered pairs in `A`, such that
`μ̃({x,y}) = μ(x,y)` for all `x, y : A`. Symmetric operations can be understood
to be fully coherent commutative operations. One can check that if `B` is a set,
then `μ` has such an extension if and only if it is commutative in the usual
algebraic sense.

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
symmetric-operation :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (lsuc lzero ⊔ l1 ⊔ l2)
symmetric-operation A B = unordered-pair A → B
```

## Properties

### The restriction of a commutative operation to the standard unordered pairs is commutative

```agda
is-commutative-symmetric-operation :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : symmetric-operation A B) →
  is-commutative (λ x y → f (standard-unordered-pair x y))
is-commutative-symmetric-operation f x y =
  ap f (is-commutative-standard-unordered-pair x y)
```

### A binary operation from `A` to `B` is commutative if and only if it extends to the unordered pairs in `A`

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Set l2)
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

  symmetric-operation-is-commutative :
    (f : A → A → type-Set B) → is-commutative f →
    symmetric-operation A (type-Set B)
  symmetric-operation-is-commutative f H (pair (pair X K) p) =
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

  compute-symmetric-operation-is-commutative :
    (f : A → A → type-Set B) (H : is-commutative f) (x y : A) →
    symmetric-operation-is-commutative f H (standard-unordered-pair x y) ＝
    f x y
  compute-symmetric-operation-is-commutative f H x y =

    htpy-universal-property-set-quotient-trunc-Prop B
      ( λ e → f (p (map-equiv e (zero-Fin 1))) (p (map-equiv e (one-Fin 1))))
      ( λ e e' →
        is-weakly-constant-on-equivalences-is-commutative f H (Fin 2) p e e'
          ( map-equiv-coprod
            ( inv-equiv
              ( equiv-ev-zero-htpy-equiv-Fin-two-ℕ (Fin-UU-Fin' 2) e e'))
            ( inv-equiv (equiv-ev-zero-htpy-equiv-Fin-two-ℕ
              ( Fin-UU-Fin' 2)
              ( e)
              ( e' ∘e equiv-succ-Fin 2)))
            ( decide-value-equiv-Fin-two-ℕ
              ( Fin-UU-Fin' 2)
              ( e')
              ( map-equiv e (zero-Fin 1)))))
      ( id-equiv)
    where
    p : Fin 2 → A
    p = pr2 (standard-unordered-pair x y)
```
