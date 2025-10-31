# Extensions of signatures

```agda
module universal-algebra.extensions-signatures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import universal-algebra.signatures

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

An
{{#concept "extension" Disambiguation="of a signature" Agda=is-extension-of-signature}}
of a [signature](universal-algebra.signatures.md) `σ` is a signature `τ` such
that `σ` [embeds](foundation-core.embeddings.md) into `τ` via an
arity-preserving map.

## Definitions

### The predicate that a signature is an extension of a signature

```agda
is-extension-of-signature :
  {l1 l2 : Level} →
  signature l1 → signature l2 → UU (l1 ⊔ l2)
is-extension-of-signature σ τ =
  Σ ( operation-signature σ ↪ operation-signature τ)
    ( λ f →
      ( (op : operation-signature σ) →
        arity-operation-signature σ op ＝
        arity-operation-signature τ (map-emb f op)))

module _
  {l1 l2 : Level}
  (σ : signature l1) (τ : signature l2)
  (ext : is-extension-of-signature σ τ)
  where

  emb-inclusion-is-extension-of-signature :
    operation-signature σ ↪ operation-signature τ
  emb-inclusion-is-extension-of-signature = pr1 ext

  inclusion-is-extension-of-signature :
    operation-signature σ → operation-signature τ
  inclusion-is-extension-of-signature =
    map-emb emb-inclusion-is-extension-of-signature

  is-emb-inclusion-is-extension-of-signature :
    is-emb inclusion-is-extension-of-signature
  is-emb-inclusion-is-extension-of-signature =
    is-emb-map-emb emb-inclusion-is-extension-of-signature

  preserves-arity-inclusion-is-extension-of-signature :
    (op : operation-signature σ) →
    arity-operation-signature σ op ＝
    arity-operation-signature τ (inclusion-is-extension-of-signature op)
  preserves-arity-inclusion-is-extension-of-signature = pr2 ext
```
