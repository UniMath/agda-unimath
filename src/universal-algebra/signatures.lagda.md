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

A signature is a collection of function symbols with a given arity.

## Definitions

### Signatures

```agda
signature : (l : Level) → UU (lsuc l)
signature (l) = Σ (UU l) (λ operations → (operations → ℕ))

operations-signature : {l : Level} → signature l → UU l
operations-signature Sig = pr1 Sig

arity-operations-signature :
  { l : Level} →
  ( Sig : signature l) →
  ( operations-signature Sig → ℕ)
arity-operations-signature Sig = pr2 Sig
```

### Extension of signatures

```agda
is-extension-signature :
  { l1 l2 : Level} →
  signature l1 → signature l2 → UU (l1 ⊔ l2)
is-extension-signature Sig1 Sig2 =
  Σ ( operations-signature Sig2 → operations-signature Sig1)
    ( λ f → is-emb f ×
      ( ( op : operations-signature Sig2) →
        arity-operations-signature Sig2 op ＝
          arity-operations-signature Sig1 (f op)))

emb-extension-signature :
  { l1 l2 : Level} →
  ( Sig1 : signature l1) →
  ( Sig2 : signature l2) →
  is-extension-signature Sig1 Sig2 →
  ( operations-signature Sig2 → operations-signature Sig1)
emb-extension-signature Sig1 Sig2 ext = pr1 ext

is-emb-extension-signature :
  { l1 l2 : Level} →
  ( Sig1 : signature l1) →
  ( Sig2 : signature l2) →
  ( ext : is-extension-signature Sig1 Sig2) →
  is-emb (emb-extension-signature Sig1 Sig2 ext)
is-emb-extension-signature Sig1 Sig2 ext = pr1 (pr2 ext)

arity-preserved-extension-signature :
  { l1 l2 : Level} →
  ( Sig1 : signature l1) →
  ( Sig2 : signature l2) →
  ( ext : is-extension-signature Sig1 Sig2) →
  ( op : operations-signature Sig2) →
  arity-operations-signature Sig2 op ＝
    arity-operations-signature Sig1
      ( emb-extension-signature Sig1 Sig2 ext op)
arity-preserved-extension-signature Sig1 Sig2 ext = pr2 (pr2 ext)
```
