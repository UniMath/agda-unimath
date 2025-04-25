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

open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
```

</details>

## Idea

A term in a signature, is an abstract representation of a well formed expression
which uses only variables and operations in the signature. For this particular
formalization, we are using de Bruijn variables.

## Definitions

### Terms

```agda
module _
  {l1 : Level} (Sg : signature l1)
  where

  data Term : UU l1 where
    var-Term : ℕ → Term
    op-Term : is-model Sg Term

  de-bruijn-variables-term : Term → list ℕ

  de-bruijn-variables-term-tuple : {n : ℕ} → tuple Term n → list ℕ

  de-bruijn-variables-term (var-Term x) = cons x nil
  de-bruijn-variables-term (op-Term f x) = de-bruijn-variables-term-tuple x

  de-bruijn-variables-term-tuple empty-tuple = nil
  de-bruijn-variables-term-tuple (x ∷ v) =
    union-list
      has-decidable-equality-ℕ
        (de-bruijn-variables-term x)
        (de-bruijn-variables-term-tuple v)

  arity-term : Term → ℕ
  arity-term t = length-list (de-bruijn-variables-term t)
```

### Assignment of variables

An assignment of variables, assigns each de Bruijn variable to an element in a
type.

```agda
  assignment : {l2 : Level} → (A : UU l2) → UU l2
  assignment A = ℕ → A
```

### Evaluation of terms

Given a model of a type `A` and an assignment of variables, any term can be
evaluated to a concrete element of the type `A`.

```agda
  eval-term :
    {l2 : Level} → {A : UU l2} →
    is-model Sg A → assignment A → Term → A

  eval-tuple :
    { l2 : Level} → {A : UU l2} {n : ℕ} →
    is-model Sg A → assignment A → tuple Term n → tuple A n

  eval-term m assign (var-Term n) = assign n
  eval-term m assign (op-Term f x) = m f (eval-tuple m assign x)

  eval-tuple m assign empty-tuple = empty-tuple
  eval-tuple m assign (x ∷ v) =
    eval-term m assign x ∷ (eval-tuple m assign v)

  eval-tuple-map-tuple-eval-term :
    { l2 : Level} {A : UU l2} {n : ℕ} →
    (m : is-model Sg A) → (assign : assignment A) → (v : tuple Term n) →
    eval-tuple m assign v ＝ map-tuple (eval-term m assign) v
  eval-tuple-map-tuple-eval-term m assign empty-tuple = refl
  eval-tuple-map-tuple-eval-term m assign (x ∷ v) =
    ap (eval-term m assign x ∷_) (eval-tuple-map-tuple-eval-term m assign v)
```

### Evaluation for constant terms

If a term `t` uses no variables, then any model on a type `A` assigns `t` to an
element of `A`.

```agda
  eval-constant-term :
    { l2 : Level} {A : UU l2} →
    ( is-model Sg A) →
    ( t : Term) →
    (de-bruijn-variables-term t ＝ nil) →
    A

  eval-constant-term-tuple :
    { l2 : Level} {A : UU l2} {n : ℕ} →
    ( is-model Sg A) →
    ( v : tuple Term n) →
    ( all-tuple (λ t → is-nil-list (de-bruijn-variables-term t)) v) →
    tuple A n

  eval-constant-term m (op-Term f x) p =
    m f (eval-constant-term-tuple m x (all-tuple-lemma x p))
    where
    all-tuple-lemma :
      { n : ℕ}
      ( v : tuple Term n) →
      ( de-bruijn-variables-term-tuple v ＝ nil) →
      all-tuple (λ t → is-nil-list (de-bruijn-variables-term t)) v
    all-tuple-lemma empty-tuple p = raise-star
    all-tuple-lemma (x ∷ v) p =
      pair
        ( pr1 (is-nil-lemma p))
        ( all-tuple-lemma v (pr2 (is-nil-lemma p)))
      where
      is-nil-lemma =
        is-nil-union-is-nil-list
          ( has-decidable-equality-ℕ)
          ( de-bruijn-variables-term x)
          ( de-bruijn-variables-term-tuple v)

  eval-constant-term-tuple m empty-tuple p = empty-tuple
  eval-constant-term-tuple m (x ∷ v) (p , p') =
    eval-constant-term m x p ∷ eval-constant-term-tuple m v p'
```

### The induced function by a term on a model

```agda
  tuple-assignment :
    {l2 : Level} {A : UU l2} →
    ℕ → (l : list ℕ) →
    tuple A (succ-ℕ (length-list l)) → assignment A
  tuple-assignment x nil (y ∷ empty-tuple) n = y
  tuple-assignment x (cons x' l) (y ∷ y' ∷ v) n
    with
    ( has-decidable-equality-ℕ x n)
  ... | inl p = y
  ... | inr p = tuple-assignment x' l (y' ∷ v) n

  induced-function-term :
    {l2 : Level} → {A : UU l2} →
    is-model Sg A → (t : Term) →
    tuple A (arity-term t) → A
  induced-function-term {l2} {A} m t v with
    ( has-decidable-equality-list
      has-decidable-equality-ℕ
      (de-bruijn-variables-term t) nil)
  ... | inl p = eval-constant-term m t p
  ... | inr p =
    eval-term m
      ( tr
        ( λ n → tuple A n → assignment A)
        ( lenght-tail-is-nonnil-list (de-bruijn-variables-term t) p)
        ( tuple-assignment
          ( head-is-nonnil-list (de-bruijn-variables-term t) p)
          ( tail-is-nonnil-list (de-bruijn-variables-term t) p))
          ( v))
      ( t)

  assignment-tuple :
    {l2 : Level} {A : UU l2} →
    (l : list ℕ) →
    assignment A →
    tuple A (length-list l)
  assignment-tuple nil f = empty-tuple
  assignment-tuple (cons x l) f = f x ∷ assignment-tuple l f
```

### Translation of terms

```agda
translation-term :
  { l1 l2 : Level} →
  ( Sg1 : signature l1) →
  ( Sg2 : signature l2) →
  is-extension-signature Sg1 Sg2 →
  Term Sg2 → Term Sg1

translation-tuple :
  { l1 l2 : Level} →
  ( Sg1 : signature l1) →
  ( Sg2 : signature l2) →
  { n : ℕ} →
  is-extension-signature Sg1 Sg2 →
  tuple (Term Sg2) n → tuple (Term Sg1) n

translation-term Sg1 Sg2 ext (var-Term x) = var-Term x
translation-term Sg1 Sg2 ext (op-Term f v) =
  op-Term (emb-extension-signature Sg1 Sg2 ext f)
    ( tr (tuple (Term Sg1))
      ( arity-preserved-extension-signature Sg1 Sg2 ext f)
      ( translation-tuple Sg1 Sg2 ext v))

translation-tuple Sg1 Sg2 ext empty-tuple = empty-tuple
translation-tuple Sg1 Sg2 ext (x ∷ v) =
  ( translation-term Sg1 Sg2 ext x) ∷
    ( translation-tuple Sg1 Sg2 ext v)
```
