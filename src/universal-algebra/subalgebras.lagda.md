# Subalgebras

```agda
module universal-algebra.subalgebras where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.tuples

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras
open import universal-algebra.models-of-signatures
open import universal-algebra.morphisms-of-models-of-signatures
open import universal-algebra.signatures
open import universal-algebra.submodels-of-signatures
open import universal-algebra.terms-over-signatures
```

</details>

## Idea

A [subset](foundation.subtypes.md) of an
[algebra](universal-algebra.algebras.md) that is closed under the
[algebraic operations](universal-algebra.signatures.md) is called a
{{#concept "subalgebra" Disambiguation="of an algebra of an algebraic theory" Agda=Subalgebra}},
and itself forms an algebra.

## Definition

```agda
subset-Algebra :
  {l1 l2 l3 : Level} (l4 : Level)
  (σ : signature l1) (T : Algebraic-Theory l2 σ) →
  Algebra l3 σ T → UU (l3 ⊔ lsuc l4)
subset-Algebra l4 σ T A = subtype l4 (type-Algebra σ T A)

module _
  {l1 l2 l3 l4 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (A : Algebra l3 σ T)
  where

  is-subalgebra-prop-subset-Algebra :
    subtype (l1 ⊔ l3 ⊔ l4) (subset-Algebra l4 σ T A)
  is-subalgebra-prop-subset-Algebra =
    is-closed-under-operations-prop-subset-Model-Of-Signature
      ( σ)
      ( model-Algebra σ T A)

  is-subalgebra-subset-Algebra :
    subset-Algebra l4 σ T A → UU (l1 ⊔ l3 ⊔ l4)
  is-subalgebra-subset-Algebra =
    is-in-subtype is-subalgebra-prop-subset-Algebra

Subalgebra :
  {l1 l2 l3 : Level} (l4 : Level) →
  (σ : signature l1) (T : Algebraic-Theory l2 σ) →
  Algebra l3 σ T → UU (l1 ⊔ l3 ⊔ lsuc l4)
Subalgebra l4 σ T A =
  type-subtype (is-subalgebra-prop-subset-Algebra {l4 = l4} σ T A)

module _
  {l1 l2 l3 l4 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (A : Algebra l3 σ T)
  ((S , is-closed-S) : Subalgebra l4 σ T A)
  where

  subset-Subalgebra : subset-Algebra l4 σ T A
  subset-Subalgebra = S
```

## Properties

### A subalgebra is an algebra

```agda
module _
  {l1 l2 l3 l4 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (A : Algebra l3 σ T)
  (SA@(S , is-closed-S) : Subalgebra l4 σ T A)
  where

  model-Subalgebra :
    Model-Of-Signature (l3 ⊔ l4) σ
  model-Subalgebra =
    model-Submodel-Of-Signature σ (model-Algebra σ T A) (S , is-closed-S)

  set-Subalgebra : Set (l3 ⊔ l4)
  set-Subalgebra = set-Model-Of-Signature σ model-Subalgebra

  is-model-set-Subalgebra :
    is-model-of-signature σ set-Subalgebra
  is-model-set-Subalgebra =
    is-model-set-Model-Of-Signature σ model-Subalgebra

  abstract
    eval-term-Subalgebra :
      {k : ℕ}
      (t : term σ k)
      (v : fin-sequence (type-subtype S) k) →
      inclusion-subtype S (eval-term σ is-model-set-Subalgebra v t) ＝
      eval-term σ (is-model-set-Algebra σ T A) (inclusion-subtype S ∘ v) t
    eval-term-Subalgebra =
      eval-term-hom-Model-Of-Signature
        ( σ)
        ( model-Subalgebra)
        ( model-Algebra σ T A)
        ( inclusion-hom-Submodel-Of-Signature σ (model-Algebra σ T A) SA)

    is-algebra-model-Subalgebra :
      is-algebra-Model-of-Signature σ T model-Subalgebra
    is-algebra-model-Subalgebra e xs =
      let
        (k , lhs , rhs) = index-abstract-equation-Algebraic-Theory σ T e
      in
        eq-type-subtype
          ( S)
          ( ( eval-term-Subalgebra lhs xs) ∙
            ( is-algebra-model-Algebra σ T A e (inclusion-subtype S ∘ xs)) ∙
            ( inv (eval-term-Subalgebra rhs xs)))

  algebra-Subalgebra : Algebra (l3 ⊔ l4) σ T
  algebra-Subalgebra =
    ( model-Subalgebra ,
      is-algebra-model-Subalgebra)
```
