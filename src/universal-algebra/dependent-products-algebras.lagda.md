# Dependent products of algebras

```agda
module universal-algebra.dependent-products-algebras where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.evaluation-functions
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.functoriality-tuples

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras
open import universal-algebra.homomorphisms-of-algebras
open import universal-algebra.morphisms-of-models-of-signatures
open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
```

</details>

## Idea

Given any family of [algebras](universal-algebra.algebras.md) in the same
[algebraic theory](universal-algebra.algebraic-theories.md), their dependent
product is an algebra in that theory.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (I : UU l3)
  (A : I → Algebra l4 σ T)
  where

  set-Π-Algebra : Set (l3 ⊔ l4)
  set-Π-Algebra = Π-Set' I (λ i → set-Algebra σ T (A i))

  type-Π-Algebra : UU (l3 ⊔ l4)
  type-Π-Algebra = type-Set set-Π-Algebra

  is-model-set-Π-Algebra : is-model-of-signature σ set-Π-Algebra
  is-model-set-Π-Algebra op fs i =
    is-model-set-Algebra σ T (A i) op (map-tuple (ev i) fs)

  model-Π-Algebra : Model-Of-Signature (l3 ⊔ l4) σ
  model-Π-Algebra = (set-Π-Algebra , is-model-set-Π-Algebra)

  hom-Π-Algebra :
    (i : I) → hom-Model-Of-Signature σ model-Π-Algebra (model-Algebra σ T (A i))
  hom-Π-Algebra i = (ev i , λ _ _ → refl)

  abstract
    htpy-is-algebra-model-Π-Algebra :
      (e : index-Algebraic-Theory σ T) →
      let
        (k , lhs , rhs) = index-abstract-equation-Algebraic-Theory σ T e
      in
        (v : fin-sequence type-Π-Algebra k) →
        eval-term σ is-model-set-Π-Algebra v lhs ~
        eval-term σ is-model-set-Π-Algebra v rhs
    htpy-is-algebra-model-Π-Algebra e v i =
      let
        (k , lhs , rhs) = index-abstract-equation-Algebraic-Theory σ T e
      in
        ( eval-term-hom-Model-Of-Signature
          ( σ)
          ( model-Π-Algebra)
          ( model-Algebra σ T (A i))
          ( hom-Π-Algebra i)
          ( lhs)
          ( v)) ∙
        ( is-algebra-model-Algebra σ T (A i) e _) ∙
        ( inv
          ( eval-term-hom-Model-Of-Signature
            ( σ)
            ( model-Π-Algebra)
            ( model-Algebra σ T (A i))
            ( hom-Π-Algebra i)
            ( rhs)
            ( v)))

    is-algebra-model-Π-Algebra :
      is-algebra-Model-Of-Signature σ T model-Π-Algebra
    is-algebra-model-Π-Algebra e v =
      eq-htpy (htpy-is-algebra-model-Π-Algebra e v)

  Π-Algebra : Algebra (l3 ⊔ l4) σ T
  Π-Algebra = (model-Π-Algebra , is-algebra-model-Π-Algebra)
```
