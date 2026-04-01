# Homomorphisms of models of signatures

```agda
module universal-algebra.homomorphisms-of-models-of-signatures where
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
open import lists.tuples

open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
```

</details>

## Idea

A
{{#concept "homomorphism" Disambiguation="models of signatures" Agda=hom-Model-of-Signature}}
from one [model](universal-algebra.models-of-signatures.md) of a
[signature](universal-algebra.signatures.md) to another is a function between
their underlying types preserving the operations of the signature.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (σ : signature l1)
  (MA : Model-Of-Signature l2 σ)
  (MB : Model-Of-Signature l3 σ)
  where

  preserves-operations-prop-Model-Of-Signature :
    subtype
      ( l1 ⊔ l2 ⊔ l3)
      ( type-Model-Of-Signature σ MA → type-Model-Of-Signature σ MB)
  preserves-operations-prop-Model-Of-Signature f =
    Π-Prop
      ( operation-signature σ)
      ( λ op →
        Π-Prop
          ( tuple
            ( type-Model-Of-Signature σ MA)
            ( arity-operation-signature σ op))
          ( λ v →
            Id-Prop
              ( set-Model-Of-Signature σ MB)
              ( f (is-model-set-Model-Of-Signature σ MA op v))
              ( is-model-set-Model-Of-Signature σ MB op (map-tuple f v))))

  preserves-operations-Model-Of-Signature :
    (type-Model-Of-Signature σ MA → type-Model-Of-Signature σ MB) →
    UU (l1 ⊔ l2 ⊔ l3)
  preserves-operations-Model-Of-Signature =
    is-in-subtype preserves-operations-prop-Model-Of-Signature

  hom-Model-of-Signature : UU (l1 ⊔ l2 ⊔ l3)
  hom-Model-of-Signature =
    type-subtype preserves-operations-prop-Model-Of-Signature

  map-hom-Model-of-Signature :
    hom-Model-of-Signature →
    type-Model-Of-Signature σ MA → type-Model-Of-Signature σ MB
  map-hom-Model-of-Signature = pr1

  preserves-operations-hom-Model-of-Signature :
    (φ : hom-Model-of-Signature) →
    preserves-operations-Model-Of-Signature (map-hom-Model-of-Signature φ)
  preserves-operations-hom-Model-of-Signature = pr2
```

## Properties

### Homomorphisms of models of signatures preserve the evaluation of terms

```agda
module _
  {l1 l2 l3 : Level}
  (σ : signature l1)
  (A : Model-Of-Signature l2 σ)
  (B : Model-Of-Signature l3 σ)
  (φ : hom-Model-of-Signature σ A B)
  where

  abstract
    eval-term-hom-Model-of-Signature :
      {k : ℕ} →
      (t : term σ k) (v : fin-sequence (type-Model-Of-Signature σ A) k) →
      map-hom-Model-of-Signature σ A B φ
        ( eval-term-Model-of-Signature σ A t v) ＝
      eval-term-Model-of-Signature σ B t
        ( map-hom-Model-of-Signature σ A B φ ∘ v)

    eval-tuple-term-hom-Model-of-Signature :
      {k n : ℕ}
      (t : tuple (term σ k) n)
      (v : fin-sequence (type-Model-Of-Signature σ A) k) →
      Eq-tuple
        ( n)
        ( map-tuple
          ( map-hom-Model-of-Signature σ A B φ)
          ( eval-tuple-term-Model-of-Signature σ A t v))
        ( eval-tuple-term-Model-of-Signature σ B t
          ( map-hom-Model-of-Signature σ A B φ ∘ v))

    eval-term-hom-Model-of-Signature (var-term i) v = refl
    eval-term-hom-Model-of-Signature (op-term op ts) v =
      ( preserves-operations-hom-Model-of-Signature σ A B φ op _) ∙
      ( ap
        ( is-model-set-Model-Of-Signature σ B op)
        ( eq-Eq-tuple _ _ _ (eval-tuple-term-hom-Model-of-Signature ts v)))

    eval-tuple-term-hom-Model-of-Signature empty-tuple v = map-raise star
    eval-tuple-term-hom-Model-of-Signature (t ∷ ts) v =
      ( eval-term-hom-Model-of-Signature t v ,
        eval-tuple-term-hom-Model-of-Signature ts v)
```
