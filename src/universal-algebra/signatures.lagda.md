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

A signature is a collection of function symbols with given arities.

## Definitions

### Signatures

```agda
signature : (l : Level) → UU (lsuc l)
signature (l) = Σ (UU l) (λ operations → (operations → ℕ))

operation-signature : {l : Level} → signature l → UU l
operation-signature σ = pr1 σ

arity-operation-signature :
  {l : Level} →
  (σ : signature l) →
  (operation-signature σ → ℕ)
arity-operation-signature σ = pr2 σ
```

### Extension of signatures

```agda
is-extension-signature :
  {l1 l2 : Level} →
  signature l1 → signature l2 → UU (l1 ⊔ l2)
is-extension-signature σ τ =
  Σ ( operation-signature τ → operation-signature σ)
    ( λ f → is-emb f ×
      ( ( op : operation-signature τ) →
        arity-operation-signature τ op ＝
          arity-operation-signature σ (f op)))

emb-extension-signature :
  {l1 l2 : Level} →
  (σ : signature l1) →
  (τ : signature l2) →
  is-extension-signature σ τ →
  (operation-signature τ → operation-signature σ)
emb-extension-signature σ τ ext = pr1 ext

is-emb-extension-signature :
  {l1 l2 : Level} →
  (σ : signature l1) →
  (τ : signature l2) →
  (ext : is-extension-signature σ τ) →
  is-emb (emb-extension-signature σ τ ext)
is-emb-extension-signature σ τ ext = pr1 (pr2 ext)

arity-preserved-extension-signature :
  {l1 l2 : Level} →
  (σ : signature l1) →
  (τ : signature l2) →
  (ext : is-extension-signature σ τ) →
  (op : operation-signature τ) →
  arity-operation-signature τ op ＝
    arity-operation-signature σ
      (emb-extension-signature σ τ ext op)
arity-preserved-extension-signature σ τ ext = pr2 (pr2 ext)
```
