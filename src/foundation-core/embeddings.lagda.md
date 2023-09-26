# Embeddings

```agda
module foundation-core.embeddings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
```

</details>

## Idea

An **embedding** from one type into another is a map that induces
[equivalences](foundation-core.equivalences.md) on
[identity types](foundation-core.identity-types.md). In other words, the
identitifications `(f x) ＝ (f y)` for an embedding `f : A → B` are in
one-to-one correspondence with the identitifications `x ＝ y`. Embeddings are
better behaved homotopically than
[injective maps](foundation-core.injective-maps.md), because the condition of
being an equivalence is a [property](foundation-core.propositions.md) under
[function extensionality](foundation.function-extensionality.md).

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-emb : (A → B) → UU (l1 ⊔ l2)
  is-emb f = (x y : A) → is-equiv (ap f {x} {y})

infix 5 _↪_
_↪_ :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A ↪ B = Σ (A → B) is-emb

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-emb : A ↪ B → A → B
  map-emb f = pr1 f

  is-emb-map-emb : (f : A ↪ B) → is-emb (map-emb f)
  is-emb-map-emb f = pr2 f

  equiv-ap-emb :
    (e : A ↪ B) {x y : A} → (x ＝ y) ≃ ((map-emb e x) ＝ (map-emb e y))
  pr1 (equiv-ap-emb e {x} {y}) = ap (map-emb e)
  pr2 (equiv-ap-emb e {x} {y}) = is-emb-map-emb e x y
```

## Examples

### The identity map is an embedding

```agda
module _
  {l : Level} {A : UU l}
  where

  is-emb-id : is-emb (id {A = A})
  is-emb-id x y = is-equiv-htpy id ap-id is-equiv-id

  id-emb : A ↪ A
  pr1 id-emb = id
  pr2 id-emb = is-emb-id
```

### To prove that a map is an embedding, a point in the domain may be assumed

```agda
module _
  {l : Level} {A : UU l} {l2 : Level} {B : UU l2} {f : A → B}
  where

  abstract
    is-emb-is-emb : (A → is-emb f) → is-emb f
    is-emb-is-emb H x y = H x x y
```
