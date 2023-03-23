# Terms over signatures

```agda
module universal-algebra.terms-over-signatures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.vectors

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
module _ {l1 : Level} (Sg : signature l1) where

  data Term : UU l1 where
    var-Term : ℕ → Term
    op-Term : is-model Sg Term
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

  eval-vec :
    { l2 : Level} → {A : UU l2} {n : ℕ} →
    is-model Sg A → assignment A → vec Term n → vec A n

  eval-term m assign (var-Term n) = assign n
  eval-term m assign (op-Term f x) = m f (eval-vec m assign x)

  eval-vec m assign empty-vec = empty-vec
  eval-vec m assign (x ∷ v) =
    eval-term m assign x ∷ (eval-vec m assign v)
```

### Translation of terms

```agda
translation-term :
  { l1 l2 : Level} →
  ( Sg1 : signature l1) →
  ( Sg2 : signature l2) →
  is-extension-signature Sg1 Sg2 →
  Term Sg2 → Term Sg1

translation-vec :
  { l1 l2 : Level} →
  ( Sg1 : signature l1) →
  ( Sg2 : signature l2) →
  { n : ℕ} →
  is-extension-signature Sg1 Sg2 →
  vec (Term Sg2) n → vec (Term Sg1) n

translation-term Sg1 Sg2 ext (var-Term x) = var-Term x
translation-term Sg1 Sg2 ext (op-Term f v) =
  op-Term (emb-extension-signature Sg1 Sg2 ext f)
    ( tr (vec (Term Sg1))
      ( arity-preserved-extension-signature Sg1 Sg2 ext f)
      ( translation-vec Sg1 Sg2 ext v))

translation-vec Sg1 Sg2 ext empty-vec = empty-vec
translation-vec Sg1 Sg2 ext (x ∷ v) =
  ( translation-term Sg1 Sg2 ext x) ∷
    ( translation-vec Sg1 Sg2 ext v)
```
