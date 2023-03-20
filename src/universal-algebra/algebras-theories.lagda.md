# Algebras

```agda
module universal-algebra.algebras-theories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import universal-algebra.abstract-equations
open import universal-algebra.algebraic-theories
open import universal-algebra.models-signatures
open import universal-algebra.signatures
open import universal-algebra.terms-signatures
```

</details>

## Idea

Given a theory, an algebra is a model on a set such that it satisfies all
equations.

## Definitions

### Algebra

```agda
module _
  { l1 : Level} ( Sig : signature l1)
  { l2 : Level } ( Th : Theory Sig l2)
  where

  is-algebra :
    { l3 : Level} →
    ( X : Model Sig l3) → UU (l2 ⊔ l3)
  is-algebra M =
    ( e : index-Theory Sig Th) →
    ( assign : assignment Sig (type-Model Sig M)) →
    eval-term Sig (is-model-set-Model Sig M) assign
      ( lhs-Abstract-Equation Sig (index-Abstract-Equation-Theory Sig Th e)) ＝
      eval-term Sig (is-model-set-Model Sig M) assign
        ( rhs-Abstract-Equation Sig (index-Abstract-Equation-Theory Sig Th e))

  Algebra :
    ( l3 : Level) →
    UU (l1 ⊔ l2 ⊔ lsuc l3)
  Algebra l3 =
    Σ ( Model Sig l3) (is-algebra)

  model-Algebra :
    { l3 : Level} →
    Algebra l3 → Model Sig l3
  model-Algebra Alg = pr1 Alg

  set-Algebra :
    { l3 : Level} →
    Algebra l3 → Set l3
  set-Algebra Alg = pr1 (pr1 Alg)

  is-model-set-Algebra :
    { l3 : Level} →
    ( Alg : Algebra l3) →
    is-model-Set Sig (set-Algebra Alg)
  is-model-set-Algebra Alg = pr2 (pr1 Alg)

  type-Algebra :
    { l3 : Level} →
    Algebra l3 → UU l3
  type-Algebra Alg =
    pr1 (pr1 (pr1 Alg))

  is-algebra-Algebra :
    { l3 : Level} →
    ( Alg : Algebra l3) →
    is-algebra (model-Algebra Alg)
  is-algebra-Algebra Alg = pr2 Alg
```

## Properties

### Being an algebra is a proposition

```agda
  is-prop-is-algebra :
    { l3 : Level} →
    ( X : Model Sig l3) →
    is-prop (is-algebra X)
  is-prop-is-algebra M =
    is-prop-Π
      ( λ e →
        ( is-prop-Π
          ( λ assign → is-set-type-Model Sig M _ _)))
```

