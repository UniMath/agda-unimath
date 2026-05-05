# Signatures

```agda
module universal-algebra.signatures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A (single-sorted, finitary, algebraic)
{{#concept "signature" Disambiguation="single-sorted, algebraic, finitary" WD="signature" WDID=Q741810 Agda=signature}}
is a [collection](foundation.dependent-pair-types.md) of function symbols with
given finite arities.

## Definitions

### Signatures

```agda
signature : (l : Level) → UU (lsuc l)
signature l = Σ (UU l) (λ operations → (operations → ℕ))

operation-signature : {l : Level} → signature l → UU l
operation-signature = pr1

arity-operation-signature :
  {l : Level} (σ : signature l) → operation-signature σ → ℕ
arity-operation-signature = pr2
```
