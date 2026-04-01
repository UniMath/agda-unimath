# Subalgebras

```agda
module universal-algebra.subalgebras where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.functoriality-tuples
open import lists.subtypes-tuples
open import lists.tuples

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras
open import universal-algebra.models-of-signatures
open import universal-algebra.morphisms-of-models-of-signatures
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
```

</details>

## Idea

A {{#concept "subalgebra" Agda=Subalgebra}} of an
[algebra](universal-algebra.algebras.md) is a [subset](foundation.subtypes.md)
of that algebra that is closed under all operations in the
[signature](universal-algebra.signatures.md) of that algebra.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (l4 : Level)
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (A : Algebra l3 σ T)
  where

  subtype-Algebra : UU (l3 ⊔ lsuc l4)
  subtype-Algebra = subtype l4 (type-Algebra σ T A)

  is-subalgebra-prop-subtype-Algebra : subtype (l1 ⊔ l3 ⊔ l4) subtype-Algebra
  is-subalgebra-prop-subtype-Algebra S =
    Π-Prop
      ( operation-signature σ)
      ( λ op →
        let
          arity = arity-operation-signature σ op
        in
          Π-Prop
            ( tuple (type-Algebra σ T A) arity)
            ( λ v →
              all-tuple-subtype S arity v ⇒
              S (is-model-set-Algebra σ T A op v)))

  Subalgebra : UU (l1 ⊔ l3 ⊔ lsuc l4)
  Subalgebra = type-subtype is-subalgebra-prop-subtype-Algebra
```

## Properties

### A subalgebra is an algebra

```agda
module _
  {l1 l2 l3 l4 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (A : Algebra l3 σ T)
  ((S , preserves-S) : Subalgebra l4 σ T A)
  where

  subtype-Subalgebra : subtype l4 (type-Algebra σ T A)
  subtype-Subalgebra = S

  set-Subalgebra : Set (l3 ⊔ l4)
  set-Subalgebra = set-subset (set-Algebra σ T A) S

  type-Subalgebra : UU (l3 ⊔ l4)
  type-Subalgebra = type-subtype S

  is-model-set-Subalgebra : is-model-of-signature σ set-Subalgebra
  is-model-set-Subalgebra op xs =
    ( is-model-set-Algebra σ T A op (map-tuple (inclusion-subtype S) xs) ,
      preserves-S
        ( op)
        ( map-tuple (inclusion-subtype S) xs)
        ( all-tuple-tuple-type-subtype S xs))

  model-of-signature-Subalgebra : Model-Of-Signature (l3 ⊔ l4) σ
  model-of-signature-Subalgebra =
    ( set-Subalgebra , is-model-set-Subalgebra)

  inclusion-hom-Subalgebra :
    hom-Model-Of-Signature
      ( σ)
      ( model-of-signature-Subalgebra)
      ( model-Algebra σ T A)
  inclusion-hom-Subalgebra =
    ( inclusion-subtype S , λ _ _ → refl)

  abstract
    eval-term-Subalgebra :
      {k : ℕ} (t : term σ k) (v : fin-sequence type-Subalgebra k) →
      inclusion-subtype S
        ( eval-term-Model-Of-Signature σ model-of-signature-Subalgebra t v) ＝
      eval-term-Model-Of-Signature σ
        ( model-Algebra σ T A)
        ( t)
        ( inclusion-subtype S ∘ v)
    eval-term-Subalgebra =
      eval-term-hom-Model-Of-Signature
        ( σ)
        ( model-of-signature-Subalgebra)
        ( model-Algebra σ T A)
        ( inclusion-hom-Subalgebra)

    is-algebra-model-Subalgebra :
      is-algebra-Model-Of-Signature σ T model-of-signature-Subalgebra
    is-algebra-model-Subalgebra i v =
      let
        (k , lhs , rhs) = index-abstract-equation-Algebraic-Theory σ T i
      in
        eq-type-subtype
          ( S)
          ( ( eval-term-Subalgebra lhs v) ∙
            ( is-algebra-model-Algebra σ T A i (inclusion-subtype S ∘ v)) ∙
            ( inv (eval-term-Subalgebra rhs v)))

  algebra-Subalgebra : Algebra (l3 ⊔ l4) σ T
  algebra-Subalgebra =
    ( model-of-signature-Subalgebra , is-algebra-model-Subalgebra)
```
