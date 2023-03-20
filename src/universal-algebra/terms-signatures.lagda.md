# Terms

```agda
module universal-algebra.terms-signatures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import linear-algebra.vectors

open import universal-algebra.models-signatures
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
module _ {l1 : Level} (Sig : signature l1) where

  data Term : UU l1 where
    var-Term : ℕ → Term
    op-Term : is-model Sig Term
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
    is-model Sig A → assignment A → Term → A

  eval-vec :
    { l2 : Level} → {A : UU l2} {n : ℕ} →
    is-model Sig A → assignment A → vec Term n → vec A n

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
  ( Sig1 : signature l1) →
  ( Sig2 : signature l2) →
  is-extension-signature Sig1 Sig2 →
  Term Sig2 → Term Sig1

translation-vec :
  { l1 l2 : Level} →
  ( Sig1 : signature l1) →
  ( Sig2 : signature l2) →
  { n : ℕ} →
  is-extension-signature Sig1 Sig2 →
  vec (Term Sig2) n → vec (Term Sig1) n

translation-term Sig1 Sig2 ext (var-Term x) = var-Term x
translation-term Sig1 Sig2 ext (op-Term f v) =
  op-Term (emb-extension-signature Sig1 Sig2 ext f)
    ( tr (vec (Term Sig1))
      ( arity-preserved-extension-signature Sig1 Sig2 ext f)
      ( translation-vec Sig1 Sig2 ext v))

translation-vec Sig1 Sig2 ext empty-vec = empty-vec
translation-vec Sig1 Sig2 ext (x ∷ v) =
  ( translation-term Sig1 Sig2 ext x) ∷
    ( translation-vec Sig1 Sig2 ext v)
```
