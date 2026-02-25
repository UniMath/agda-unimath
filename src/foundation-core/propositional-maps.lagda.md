# Propositional maps

```agda
module foundation-core.propositional-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

A map is said to be **propositional** if its
[fibers](foundation-core.fibers-of-maps.md) are
[propositions](foundation-core.propositions.md). This condition is the same as
the condition of being a
[`-1`-truncated map](foundation-core.truncated-maps.md), and it is
[equivalent](foundation-core.equivalences.md) to being an
[embedding](foundation-core.embeddings.md).

**Note:** Of the three equivalent conditions mentioned above, propositional
maps, `-1`-truncated maps, and embeddings, the central notion of in the
agda-unimath library is that of embedding. This means that most infrastructure
is available for embeddings, and that it is easy to convert from any of the
other two notions to the notion of embedding.

## Definitions

### The predicate of being a propositional map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-map : (A → B) → UU (l1 ⊔ l2)
  is-prop-map f = (b : B) → is-prop (fiber f b)
```

### The type of propositional maps

```agda
module _
  {l1 l2 : Level}
  where

  prop-map : (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
  prop-map A B = Σ (A → B) is-prop-map

  module _
    {A : UU l1} {B : UU l2} (f : prop-map A B)
    where

    map-prop-map : A → B
    map-prop-map = pr1 f

    is-prop-map-prop-map : is-prop-map map-prop-map
    is-prop-map-prop-map = pr2 f
```

## Properties

### The fibers of a map are propositions if and only if it is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  abstract
    is-emb-is-prop-map : is-prop-map f → is-emb f
    is-emb-is-prop-map is-prop-map-f x =
      fundamental-theorem-id
        ( is-contr-equiv'
          ( fiber f (f x))
          ( equiv-fiber f (f x))
          ( is-proof-irrelevant-is-prop (is-prop-map-f (f x)) (x , refl)))
        ( λ _ → ap f)

  abstract
    is-prop-map-is-emb : is-emb f → is-prop-map f
    is-prop-map-is-emb is-emb-f y =
      is-prop-is-proof-irrelevant α
      where
      α : (t : fiber f y) → is-contr (fiber f y)
      α (x , refl) =
        is-contr-equiv
          ( fiber' f (f x))
          ( equiv-fiber f (f x))
          ( fundamental-theorem-id' (λ _ → ap f) (is-emb-f x))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  emb-prop-map : prop-map A B → A ↪ B
  pr1 (emb-prop-map (f , p)) = f
  pr2 (emb-prop-map (f , p)) = is-emb-is-prop-map p

  prop-map-emb : A ↪ B → prop-map A B
  pr1 (prop-map-emb (f , p)) = f
  pr2 (prop-map-emb (f , p)) = is-prop-map-is-emb p

  is-prop-map-emb : (f : A ↪ B) → is-prop-map (map-emb f)
  is-prop-map-emb f = is-prop-map-is-emb (is-emb-map-emb f)

  is-prop-map-emb' : (f : A ↪ B) → (b : B) → is-prop (fiber' (map-emb f) b)
  is-prop-map-emb' f y =
    is-prop-equiv' (equiv-fiber (map-emb f) y) (is-prop-map-emb f y)

  fiber-emb-Prop : A ↪ B → B → Prop (l1 ⊔ l2)
  pr1 (fiber-emb-Prop f y) = fiber (map-emb f) y
  pr2 (fiber-emb-Prop f y) = is-prop-map-emb f y

  fiber-emb-Prop' : A ↪ B → B → Prop (l1 ⊔ l2)
  pr1 (fiber-emb-Prop' f y) = fiber' (map-emb f) y
  pr2 (fiber-emb-Prop' f y) = is-prop-map-emb' f y
```

### The identity function is propositional

```agda
is-prop-map-id : {l : Level} {X : UU l} → is-prop-map (id' X)
is-prop-map-id = is-prop-map-is-emb is-emb-id
```
