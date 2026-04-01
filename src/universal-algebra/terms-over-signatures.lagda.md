# Terms over signatures

```agda
module universal-algebra.terms-over-signatures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import lists.equivalence-tuples-finite-sequences
open import lists.finite-sequences
open import lists.functoriality-tuples
open import lists.tuples

open import univalent-combinatorics.standard-finite-types

open import universal-algebra.extensions-signatures
open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
```

</details>

## Idea

A
{{#concept "term" Disambiguation="over a single-sorted finitary algebraic signature" Agda=term}}
over a
[single-sorted finitary algebraic signature](universal-algebra.signatures.md),
is an abstract representation of a well-formed expression which uses only
variables and operations in the signature.

In this treatment, a term is parameterized by the number of variables required
to evaluate it.

## Definitions

### Terms

```agda
module _
  {l1 : Level} (σ : signature l1)
  where

  data term (k : ℕ) : UU l1 where
    var-term : Fin k → term k
    op-term : is-model-of-signature-type σ (term k)
```

### Evaluation of terms

Given a model of a type `A` and an assignment of variables, any term can be
evaluated to a concrete element of the type `A`.

```agda
module _
  {l1 : Level} (σ : signature l1)
  where

  eval-term :
    {l2 : Level} → {A : UU l2} {k : ℕ} →
    is-model-of-signature-type σ A → fin-sequence A k → term σ k → A

  eval-tuple-term :
    {l2 : Level} → {A : UU l2} {m n : ℕ} →
    is-model-of-signature-type σ A →
    fin-sequence A m → tuple (term σ m) n → tuple A n

  eval-term m assign (var-term n) = assign n
  eval-term m assign (op-term f x) = m f (eval-tuple-term m assign x)

  -- explicit definition required for termination checking;
  -- we can't use map-tuple
  eval-tuple-term m assign empty-tuple = empty-tuple
  eval-tuple-term m assign (x ∷ v) =
    eval-term m assign x ∷ (eval-tuple-term m assign v)

  abstract
    eval-tuple-map-tuple-eval-term :
      {l2 : Level} {A : UU l2} {k n : ℕ} →
      (m : is-model-of-signature-type σ A)
      (assign : fin-sequence A k)
      (v : tuple (term σ k) n) →
      eval-tuple-term m assign v ＝ map-tuple (eval-term m assign) v
    eval-tuple-map-tuple-eval-term m assign empty-tuple = refl
    eval-tuple-map-tuple-eval-term m assign (x ∷ v) =
      ap (eval-term m assign x ∷_) (eval-tuple-map-tuple-eval-term m assign v)
```

### The induced function by a term on a model

```agda
module _
  {l1 : Level} (σ : signature l1)
  where

  eval-term-tuple :
    {l2 : Level} {A : UU l2} {k : ℕ} →
    is-model-of-signature-type σ A → term σ k →
    tuple A k → A
  eval-term-tuple m t v =
    eval-term σ m (fin-sequence-tuple _ v) t
```

### Translation of terms

```agda
module _
  {l1 l2 : Level}
  (σ : signature l1)
  (τ : signature l2)
  (E : is-extension-of-signature σ τ)
  {k : ℕ}
  where

  translation-term : term σ k → term τ k

  translation-tuple-term : {n : ℕ} → tuple (term σ k) n → tuple (term τ k) n

  translation-term (var-term x) =
    var-term x
  translation-term (op-term f v) =
    op-term
      ( inclusion-is-extension-of-signature σ τ E f)
      ( tr
        ( tuple (term τ k))
        ( preserves-arity-inclusion-is-extension-of-signature σ τ E f)
        ( translation-tuple-term v))

  translation-tuple-term empty-tuple =
    empty-tuple
  translation-tuple-term (x ∷ v) =
    (translation-term x) ∷ (translation-tuple-term v)
```
