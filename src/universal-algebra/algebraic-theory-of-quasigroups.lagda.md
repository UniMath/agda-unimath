# The algebraic theory of quasigroups

```agda
{-# OPTIONS --lossy-unification #-}

module universal-algebra.algebraic-theory-of-quasigroups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.quasigroups

open import lists.tuples

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-of-theories
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures

```

</details>

## Idea

There is an algebraic theory of [quasigroups](group-theory.quasigroups.md). The
type of all such algebras is equivalent to the type of quasigroups.

## Definition

### The algebra of quasigroups

```agda
data quasigroup-ops : UU lzero where
  mul-quasigroup-op left-div-quasigroup-op right-div-quasigroup-op : quasigroup-ops

quasigroup-signature : signature lzero
pr1 quasigroup-signature = quasigroup-ops
pr2 quasigroup-signature _ = 2

data quasigroup-laws : UU lzero where
  is-left-cancellative-right-div-quasigroup-laws : quasigroup-laws
  is-right-cancellative-right-div-quasigroup-laws : quasigroup-laws
  is-left-cancellative-left-div-quasigroup-laws : quasigroup-laws
  is-right-cancellative-left-div-quasigroup-laws : quasigroup-laws

quasigroup-Theory : Theory quasigroup-signature lzero
pr1 quasigroup-Theory = quasigroup-laws
pr2 quasigroup-Theory =
  λ where
  is-left-cancellative-right-div-quasigroup-laws →
    ( var-Term 1) , op-Term mul-quasigroup-op
    ( op-Term right-div-quasigroup-op
    (( var-Term 1) ∷ (var-Term 0) ∷ empty-tuple) ∷ (var-Term 0) ∷ empty-tuple)
  is-right-cancellative-right-div-quasigroup-laws →
    ( var-Term 1) , op-Term right-div-quasigroup-op
    (( op-Term mul-quasigroup-op ((var-Term 1) ∷ (var-Term 0) ∷ empty-tuple)) ∷
    ( var-Term 0) ∷ empty-tuple)
  is-left-cancellative-left-div-quasigroup-laws →
    ( var-Term 1) , op-Term mul-quasigroup-op
    ( var-Term 0 ∷ (op-Term left-div-quasigroup-op
    (( var-Term 0) ∷ (var-Term 1) ∷ empty-tuple)) ∷ empty-tuple)
  is-right-cancellative-left-div-quasigroup-laws →
    ( var-Term 1) , (op-Term left-div-quasigroup-op
    (( var-Term 0) ∷ ((op-Term mul-quasigroup-op
    (( var-Term 0) ∷ (var-Term 1) ∷ empty-tuple)) ∷ empty-tuple)))

quasigroup-Algebra : (l : Level) → UU (lsuc l)
quasigroup-Algebra l = Algebra quasigroup-signature quasigroup-Theory l
```

## Properties

### The algebra of quasigroups is equivalent to the type of quasigroups

```agda
module _
  {l : Level}
  where

  quasigroup-Algebra-Quasigroup : quasigroup-Algebra l → Quasigroup l
  pr1 (quasigroup-Algebra-Quasigroup ((A , _) , _)) = A
  pr1 (pr2 (quasigroup-Algebra-Quasigroup ((A , models-A) , satisfies-A))) x y =
    models-A mul-quasigroup-op (x ∷ y ∷ empty-tuple)
  pr1 (pr2 (pr2 (quasigroup-Algebra-Quasigroup
    (( A , models-A) , satisfies-A)))) x y =
      models-A left-div-quasigroup-op (x ∷ y ∷ empty-tuple)
  pr1 (pr2 (pr2 (pr2 (quasigroup-Algebra-Quasigroup
    (( A , models-A) , satisfies-A))))) x y =
      models-A right-div-quasigroup-op (x ∷ y ∷ empty-tuple)
  pr1 (pr1 (pr2 (pr2 (pr2 (pr2 (quasigroup-Algebra-Quasigroup
    (( A , models-A) , satisfies-A))))))) x y =
      satisfies-A is-left-cancellative-left-div-quasigroup-laws
      ( λ {0 → x ; (succ-ℕ n) → y})
  pr2 (pr1 (pr2 (pr2 (pr2 (pr2 (quasigroup-Algebra-Quasigroup
    (( A , models-A) , satisfies-A))))))) x y =
      satisfies-A is-right-cancellative-left-div-quasigroup-laws
      ( λ {0 → x ; (succ-ℕ n) → y})
  pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (quasigroup-Algebra-Quasigroup
    (( A , models-A) , satisfies-A))))))) x y =
      satisfies-A is-left-cancellative-right-div-quasigroup-laws
      ( λ {0 → x ; (succ-ℕ n) → y})
  pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (quasigroup-Algebra-Quasigroup
    (( A , models-A) , satisfies-A))))))) x y =
      satisfies-A is-right-cancellative-right-div-quasigroup-laws
      ( λ {0 → x ; (succ-ℕ n) → y})

  Quasigroup-quasigroup-Algebra : Quasigroup l → quasigroup-Algebra l
  pr1 (pr1 (Quasigroup-quasigroup-Algebra (Q , _))) = Q
  pr2 (pr1 (Quasigroup-quasigroup-Algebra Q)) =
    λ where
    mul-quasigroup-op (x ∷ y ∷ empty-tuple) → mul-Quasigroup Q x y
    left-div-quasigroup-op (x ∷ y ∷ empty-tuple) → left-div-Quasigroup Q x y
    right-div-quasigroup-op (x ∷ y ∷ empty-tuple) → right-div-Quasigroup Q x y
  pr2 (Quasigroup-quasigroup-Algebra Q)
    is-left-cancellative-right-div-quasigroup-laws assign =
      is-left-cancellative-right-div-Quasigroup Q (assign 0) (assign 1)
  pr2 (Quasigroup-quasigroup-Algebra Q)
    is-right-cancellative-right-div-quasigroup-laws assign =
      is-right-cancellative-right-div-Quasigroup Q (assign 0) (assign 1)
  pr2 (Quasigroup-quasigroup-Algebra Q)
    is-left-cancellative-left-div-quasigroup-laws assign =
      is-left-cancellative-left-div-Quasigroup Q (assign 0) (assign 1)
  pr2 (Quasigroup-quasigroup-Algebra Q)
    is-right-cancellative-left-div-quasigroup-laws assign =
      is-right-cancellative-left-div-Quasigroup Q (assign 0) (assign 1)

  abstract
    equiv-quasigroup-Algebra-Quasigroup : quasigroup-Algebra l ≃ Quasigroup l
    pr1 equiv-quasigroup-Algebra-Quasigroup = quasigroup-Algebra-Quasigroup
    pr1 (pr1 (pr2 equiv-quasigroup-Algebra-Quasigroup)) =
      Quasigroup-quasigroup-Algebra
    pr2 (pr1 (pr2 equiv-quasigroup-Algebra-Quasigroup)) = λ _ → refl
    pr1 (pr2 (pr2 equiv-quasigroup-Algebra-Quasigroup)) =
      Quasigroup-quasigroup-Algebra
    pr2 (pr2 (pr2 equiv-quasigroup-Algebra-Quasigroup)) A =
        eq-pair-Σ (eq-pair-Σ refl (eq-htpy
        ( λ where
          mul-quasigroup-op → eq-htpy
            ( λ where (x ∷ y ∷ empty-tuple) → refl)
          left-div-quasigroup-op → eq-htpy
            ( λ where (x ∷ y ∷ empty-tuple) → refl)
          right-div-quasigroup-op → eq-htpy
            ( λ where (x ∷ y ∷ empty-tuple) → refl))))
        ( eq-is-prop (is-prop-is-algebra quasigroup-signature quasigroup-Theory
        ( model-Algebra quasigroup-signature quasigroup-Theory A)))
```
