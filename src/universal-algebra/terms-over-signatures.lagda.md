# Terms over signatures

```agda
module universal-algebra.terms-over-signatures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import lists.functoriality-tuples
open import lists.lists
open import lists.lists-discrete-types
open import lists.tuples

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

For this particular formalization, we are using de Bruijn variables.

## Definitions

### Terms

```agda
module _
  {l1 : Level} (σ : signature l1)
  where

  data term : UU l1 where
    var-term : ℕ → term
    op-term : is-model-of-signature-type σ term

  de-bruijn-variables-term : term → list ℕ

  de-bruijn-variables-tuple-term : {n : ℕ} → tuple term n → list ℕ

  de-bruijn-variables-term (var-term x) = cons x nil
  de-bruijn-variables-term (op-term f x) = de-bruijn-variables-tuple-term x

  de-bruijn-variables-tuple-term empty-tuple = nil
  de-bruijn-variables-tuple-term (x ∷ v) =
    union-list
      has-decidable-equality-ℕ
        (de-bruijn-variables-term x)
        (de-bruijn-variables-tuple-term v)

  arity-term : term → ℕ
  arity-term t = length-list (de-bruijn-variables-term t)
```

### Assignment of variables

An assignment of variables, assigns each de Bruijn variable to an element in a
type.

```agda
module _
  {l1 : Level} (σ : signature l1)
  where

  assignment : {l2 : Level} → UU l2 → UU l2
  assignment A = ℕ → A
```

### Evaluation of terms

Given a model of a type `A` and an assignment of variables, any term can be
evaluated to a concrete element of the type `A`.

```agda
module _
  {l1 : Level} (σ : signature l1)
  where

  eval-term :
    {l2 : Level} → {A : UU l2} →
    is-model-of-signature-type σ A → assignment σ A → term σ → A

  eval-tuple-term :
    {l2 : Level} → {A : UU l2} {n : ℕ} →
    is-model-of-signature-type σ A →
    assignment σ A → tuple (term σ) n → tuple A n

  eval-term m assign (var-term n) = assign n
  eval-term m assign (op-term f x) = m f (eval-tuple-term m assign x)

  eval-tuple-term m assign empty-tuple = empty-tuple
  eval-tuple-term m assign (x ∷ v) =
    eval-term m assign x ∷ (eval-tuple-term m assign v)

  eval-tuple-map-tuple-eval-term :
    {l2 : Level} {A : UU l2} {n : ℕ} →
    (m : is-model-of-signature-type σ A)
    (assign : assignment σ A)
    (v : tuple (term σ) n) →
    eval-tuple-term m assign v ＝ map-tuple (eval-term m assign) v
  eval-tuple-map-tuple-eval-term m assign empty-tuple = refl
  eval-tuple-map-tuple-eval-term m assign (x ∷ v) =
    ap (eval-term m assign x ∷_) (eval-tuple-map-tuple-eval-term m assign v)
```

### Evaluation for constant terms

If a term `t` uses no variables, then any model on a type `A` assigns `t` to an
element of `A`.

```agda
module _
  {l1 : Level} (σ : signature l1)
  where

  eval-constant-term :
    {l2 : Level} {A : UU l2} →
    is-model-of-signature-type σ A →
    (t : term σ) →
    (de-bruijn-variables-term σ t ＝ nil) →
    A

  eval-constant-tuple-term :
    {l2 : Level} {A : UU l2} {n : ℕ} →
    (is-model-of-signature-type σ A) →
    (v : tuple (term σ) n) →
    (all-tuple (λ t → is-nil-list (de-bruijn-variables-term σ t)) v) →
    tuple A n

  eval-constant-term m (op-term f x) p =
    m f (eval-constant-tuple-term m x (all-tuple-lemma x p))
    where
    all-tuple-lemma :
      { n : ℕ}
      ( v : tuple (term σ) n) →
      ( de-bruijn-variables-tuple-term σ v ＝ nil) →
      all-tuple (λ t → is-nil-list (de-bruijn-variables-term σ t)) v
    all-tuple-lemma empty-tuple p = raise-star
    all-tuple-lemma (x ∷ v) p =
      pair
        ( pr1 (is-nil-lemma p))
        ( all-tuple-lemma v (pr2 (is-nil-lemma p)))
      where
      is-nil-lemma =
        is-nil-union-is-nil-list
          ( has-decidable-equality-ℕ)
          ( de-bruijn-variables-term σ x)
          ( de-bruijn-variables-tuple-term σ v)

  eval-constant-tuple-term m empty-tuple p = empty-tuple
  eval-constant-tuple-term m (x ∷ v) (p , p') =
    eval-constant-term m x p ∷ eval-constant-tuple-term m v p'
```

### The induced function by a term on a model

```agda
module _
  {l1 : Level} (σ : signature l1)
  where

  tuple-assignment :
    {l2 : Level} {A : UU l2} →
    ℕ → (l : list ℕ) →
    tuple A (succ-ℕ (length-list l)) → assignment σ A
  tuple-assignment x nil (y ∷ empty-tuple) n = y
  tuple-assignment x (cons x' l) (y ∷ y' ∷ v) n
    with
    ( has-decidable-equality-ℕ x n)
  ... | inl p = y
  ... | inr p = tuple-assignment x' l (y' ∷ v) n

  induced-function-term :
    {l2 : Level} → {A : UU l2} →
    is-model-of-signature-type σ A → (t : term σ) →
    tuple A (arity-term σ t) → A
  induced-function-term {l2} {A} m t v with
    ( has-decidable-equality-list
      has-decidable-equality-ℕ
      (de-bruijn-variables-term σ t) nil)
  ... | inl p = eval-constant-term σ m t p
  ... | inr p =
    eval-term σ m
      ( tr
        ( λ n → tuple A n → assignment σ A)
        ( lenght-tail-is-nonnil-list (de-bruijn-variables-term σ t) p)
        ( tuple-assignment
          ( head-is-nonnil-list (de-bruijn-variables-term σ t) p)
          ( tail-is-nonnil-list (de-bruijn-variables-term σ t) p))
          ( v))
      ( t)

  assignment-tuple :
    {l2 : Level} {A : UU l2} →
    (l : list ℕ) →
    assignment σ A →
    tuple A (length-list l)
  assignment-tuple nil f = empty-tuple
  assignment-tuple (cons x l) f = f x ∷ assignment-tuple l f
```

### Translation of terms

```agda
module _
  {l1 l2 : Level}
  (σ : signature l1)
  (τ : signature l2)
  (E : is-extension-of-signature σ τ)
  where

  translation-term : term σ → term τ

  translation-tuple-term : {n : ℕ} → tuple (term σ) n → tuple (term τ) n

  translation-term (var-term x) =
    var-term x
  translation-term (op-term f v) =
    op-term
      ( inclusion-is-extension-of-signature σ τ E f)
      ( tr
        ( tuple (term τ))
        ( preserves-arity-inclusion-is-extension-of-signature σ τ E f)
        ( translation-tuple-term v))

  translation-tuple-term empty-tuple =
    empty-tuple
  translation-tuple-term (x ∷ v) =
    (translation-term x) ∷ (translation-tuple-term v)
```
