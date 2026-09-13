# Dependent products of cumulative large sets

```agda
module foundation.dependent-products-cumulative-large-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cumulative-large-sets
open import foundation.dependent-products-large-similarity-relations
open import foundation.large-binary-relations
open import foundation.large-similarity-relations
open import foundation.universe-levels
```

</details>

## Idea

The dependent product of a family of
[cumulative large sets](foundation.cumulative-large-sets.md) is a cumulative
large set.

## Definition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {l0 : Level}
  (I : UU l0)
  (S : I → Cumulative-Large-Set α β)
  where

  type-Π-Cumulative-Large-Set : (l : Level) → UU (α l ⊔ l0)
  type-Π-Cumulative-Large-Set l =
    (i : I) → type-Cumulative-Large-Set (S i) l

  large-similarity-relation-Π-Cumulative-Large-Set :
    Large-Similarity-Relation
      ( λ l1 l2 → l0 ⊔ β l1 l2)
      ( type-Π-Cumulative-Large-Set)
  large-similarity-relation-Π-Cumulative-Large-Set =
    Π-Large-Similarity-Relation
      ( I)
      ( λ i → type-Cumulative-Large-Set (S i))
      ( λ i → large-similarity-relation-Cumulative-Large-Set (S i))

  sim-Π-Cumulative-Large-Set :
    Large-Relation
      ( λ l1 l2 → l0 ⊔ β l1 l2)
      ( type-Π-Cumulative-Large-Set)
  sim-Π-Cumulative-Large-Set =
    sim-Large-Similarity-Relation
      ( large-similarity-relation-Π-Cumulative-Large-Set)

  raise-Π-Cumulative-Large-Set :
    {l0 : Level} (l : Level) →
    type-Π-Cumulative-Large-Set l0 → type-Π-Cumulative-Large-Set (l0 ⊔ l)
  raise-Π-Cumulative-Large-Set l f i = raise-Cumulative-Large-Set (S i) l (f i)

  sim-raise-Π-Cumulative-Large-Set :
    {l0 : Level} (l : Level) (f : type-Π-Cumulative-Large-Set l0) →
    sim-Π-Cumulative-Large-Set f (raise-Π-Cumulative-Large-Set l f)
  sim-raise-Π-Cumulative-Large-Set l f i =
    sim-raise-Cumulative-Large-Set (S i) l (f i)

  Π-Cumulative-Large-Set :
    Cumulative-Large-Set (λ l → l0 ⊔ α l) (λ l1 l2 → l0 ⊔ β l1 l2)
  Π-Cumulative-Large-Set =
    λ where
      .type-Cumulative-Large-Set → type-Π-Cumulative-Large-Set
      .large-similarity-relation-Cumulative-Large-Set →
        large-similarity-relation-Π-Cumulative-Large-Set
      .raise-Cumulative-Large-Set →
        raise-Π-Cumulative-Large-Set
      .sim-raise-Cumulative-Large-Set →
        sim-raise-Π-Cumulative-Large-Set
```
