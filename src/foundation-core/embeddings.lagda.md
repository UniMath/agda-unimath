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

An {{#concept "embedding" Agda=_↪_ WD="embedding" WDID=Q980509}} from one type
into another is a map that induces
[equivalences](foundation-core.equivalences.md) on
[identity types](foundation-core.identity-types.md). In other words, the
identitifications `(f x) ＝ (f y)` for an embedding `f : A → B` are in
one-to-one correspondence with the identifications `x ＝ y`. Embeddings are
better behaved homotopically than
[injective maps](foundation-core.injective-maps.md), because the condition of
being an equivalence is a [property](foundation-core.propositions.md) under
[function extensionality](foundation.function-extensionality.md).

## Definitions

### The predicate on maps of being embeddings

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-emb : (A → B) → UU (l1 ⊔ l2)
  is-emb f = (x y : A) → is-equiv (ap f {x} {y})

  equiv-ap-is-emb :
    {f : A → B} (e : is-emb f) {x y : A} → (x ＝ y) ≃ (f x ＝ f y)
  pr1 (equiv-ap-is-emb {f} e) = ap f
  pr2 (equiv-ap-is-emb {f} e {x} {y}) = e x y

  inv-equiv-ap-is-emb :
    {f : A → B} (e : is-emb f) {x y : A} → (f x ＝ f y) ≃ (x ＝ y)
  inv-equiv-ap-is-emb e = inv-equiv (equiv-ap-is-emb e)
```

### The type of embeddings

```agda
infix 5 _↪_
_↪_ :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A ↪ B = Σ (A → B) is-emb

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-emb : A ↪ B → A → B
  map-emb = pr1

  is-emb-map-emb : (f : A ↪ B) → is-emb (map-emb f)
  is-emb-map-emb = pr2

  equiv-ap-emb :
    (e : A ↪ B) {x y : A} → (x ＝ y) ≃ (map-emb e x ＝ map-emb e y)
  equiv-ap-emb e = equiv-ap-is-emb (is-emb-map-emb e)

  inv-equiv-ap-emb :
    (e : A ↪ B) {x y : A} → (map-emb e x ＝ map-emb e y) ≃ (x ＝ y)
  inv-equiv-ap-emb e = inv-equiv (equiv-ap-emb e)
```

### The type of embeddings into a type

```agda
Emb : (l1 : Level) {l2 : Level} (B : UU l2) → UU (lsuc l1 ⊔ l2)
Emb l1 B = Σ (UU l1) (λ A → A ↪ B)

module _
  {l1 l2 : Level} {B : UU l2} (f : Emb l1 B)
  where

  type-Emb : UU l1
  type-Emb = pr1 f

  emb-Emb : type-Emb ↪ B
  emb-Emb = pr2 f

  map-Emb : type-Emb → B
  map-Emb = map-emb emb-Emb

  is-emb-map-Emb : is-emb map-Emb
  is-emb-map-Emb = is-emb-map-emb emb-Emb
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
