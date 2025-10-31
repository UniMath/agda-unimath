# Abstract equations over signatures

```agda
module universal-algebra.abstract-equations-over-signatures where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

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
  abstract-equation = term σ × term σ

  lhs-abstract-equation : abstract-equation → term σ
  lhs-abstract-equation = pr1

  rhs-abstract-equation : abstract-equation → term σ
  rhs-abstract-equation = pr2
```
