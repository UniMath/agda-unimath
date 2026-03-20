# Abstract equations over signatures

```agda
module universal-algebra.abstract-equations-over-signatures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import universal-algebra.extensions-signatures
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
```

</details>

## Idea

An
{{#concept "abstract equation" Disambiguation="over a single-sorted finitary algebraic signature" Agda=abstract-equation}}
over a
[single-sorted finitary algebraic signature](universal-algebra.signatures.md)
`σ` is a statement of the form "`x` equals `y`", where `x` and `y` are
[terms](universal-algebra.terms-over-signatures.md) over `σ`. Thus, the data of
an abstract equation is simply two terms over a common signature.

## Definitions

### Abstract equations

```agda
module _
  {l1 : Level} (σ : signature l1)
  where

  abstract-equation : UU l1
  abstract-equation = Σ ℕ (λ k → term σ k × term σ k)

module _
  {l : Level} (σ : signature l) ((k , lhs , rhs) : abstract-equation σ)
  where

  arity-abstract-equation : ℕ
  arity-abstract-equation = k

  lhs-abstract-equation : term σ arity-abstract-equation
  lhs-abstract-equation = lhs

  rhs-abstract-equation : term σ arity-abstract-equation
  rhs-abstract-equation = rhs
```

## Properties

### Translation of equations

```agda
module _
  {l1 l2 : Level}
  (σ : signature l1)
  (τ : signature l2)
  (E : is-extension-of-signature σ τ)
  {k : ℕ}
  where

  translation-abstract-equation :
    abstract-equation σ → abstract-equation τ
  translation-abstract-equation (k , lhs , rhs) =
    ( k , translation-term σ τ E lhs , translation-term σ τ E rhs)
```
