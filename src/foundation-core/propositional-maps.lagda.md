# Propositional maps

```agda
module foundation-core.propositional-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.functions
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.fundamental-theorem-of-identity-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.universe-levels
```

</details>

## Idea

A map is said to be propositional if its fibers are propositions. This condition is equivalent to being an embedding.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-map : (A → B) → UU (l1 ⊔ l2)
  is-prop-map f = (b : B) → is-prop (fib f b)
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
          ( fib f (f x))
          ( equiv-fib f (f x))
          ( is-proof-irrelevant-is-prop (is-prop-map-f (f x)) (pair x refl)))
        ( λ y → ap f)

  abstract
    is-prop-map-is-emb : is-emb f → is-prop-map f
    is-prop-map-is-emb is-emb-f y =
      is-prop-is-proof-irrelevant α
      where
      α : (t : fib f y) → is-contr (fib f y)
      α (pair x refl) =
        is-contr-equiv
          ( fib' f (f x))
          ( equiv-fib f (f x))
          ( fundamental-theorem-id'
            ( λ y → ap f)
            ( λ y → is-emb-f x y))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-map-emb : (f : A ↪ B) → is-prop-map (map-emb f)
  is-prop-map-emb f = is-prop-map-is-emb (is-emb-map-emb f)

  is-prop-map-emb' : (f : A ↪ B) → (b : B) → is-prop (fib' (map-emb f) b)
  is-prop-map-emb' f y =
    is-prop-equiv' (equiv-fib (map-emb f) y) (is-prop-map-emb f y)

  fib-emb-Prop : A ↪ B → B → Prop (l1 ⊔ l2)
  pr1 (fib-emb-Prop f y) = fib (map-emb f) y
  pr2 (fib-emb-Prop f y) = is-prop-map-emb f y

  fib-emb-Prop' : A ↪ B → B → Prop (l1 ⊔ l2)
  pr1 (fib-emb-Prop' f y) = fib' (map-emb f) y
  pr2 (fib-emb-Prop' f y) = is-prop-map-emb' f y
```
