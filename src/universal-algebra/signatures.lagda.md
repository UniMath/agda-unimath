# Signatures

```agda
open import foundation.function-extensionality-axiom

module
  universal-algebra.signatures
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types funext
open import foundation.dependent-pair-types
open import foundation.embeddings funext
open import foundation.identity-types funext
open import foundation.universe-levels
```

</details>

## Idea

A signature is a collection of function symbols with given arities.

## Definitions

### Signatures

```agda
signature : (l : Level) → UU (lsuc l)
signature (l) = Σ (UU l) (λ operations → (operations → ℕ))

operation-signature : {l : Level} → signature l → UU l
operation-signature Sg = pr1 Sg

arity-operation-signature :
  { l : Level} →
  ( Sg : signature l) →
  ( operation-signature Sg → ℕ)
arity-operation-signature Sg = pr2 Sg
```

### Extension of signatures

```agda
is-extension-signature :
  { l1 l2 : Level} →
  signature l1 → signature l2 → UU (l1 ⊔ l2)
is-extension-signature Sg1 Sg2 =
  Σ ( operation-signature Sg2 → operation-signature Sg1)
    ( λ f → is-emb f ×
      ( ( op : operation-signature Sg2) →
        arity-operation-signature Sg2 op ＝
          arity-operation-signature Sg1 (f op)))

emb-extension-signature :
  { l1 l2 : Level} →
  ( Sg1 : signature l1) →
  ( Sg2 : signature l2) →
  is-extension-signature Sg1 Sg2 →
  ( operation-signature Sg2 → operation-signature Sg1)
emb-extension-signature Sg1 Sg2 ext = pr1 ext

is-emb-extension-signature :
  { l1 l2 : Level} →
  ( Sg1 : signature l1) →
  ( Sg2 : signature l2) →
  ( ext : is-extension-signature Sg1 Sg2) →
  is-emb (emb-extension-signature Sg1 Sg2 ext)
is-emb-extension-signature Sg1 Sg2 ext = pr1 (pr2 ext)

arity-preserved-extension-signature :
  { l1 l2 : Level} →
  ( Sg1 : signature l1) →
  ( Sg2 : signature l2) →
  ( ext : is-extension-signature Sg1 Sg2) →
  ( op : operation-signature Sg2) →
  arity-operation-signature Sg2 op ＝
    arity-operation-signature Sg1
      ( emb-extension-signature Sg1 Sg2 ext op)
arity-preserved-extension-signature Sg1 Sg2 ext = pr2 (pr2 ext)
```
