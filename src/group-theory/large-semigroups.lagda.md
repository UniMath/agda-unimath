# Large semigroups

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.large-semigroups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.sets funext univalence
open import foundation.universe-levels

open import group-theory.semigroups funext univalence
```

</details>

## Idea

A **large semigroup** with universe indexing function `α : Level → Level`
consists of:

- For each universe level `l` a set `X l : UU (α l)`
- For any two universe levels `l1` and `l2` a binary operation
  `μ l1 l2 : X l1 → X l2 → X (l1 ⊔ l2)` satisfying the following associativity
  law:

```text
  μ (l1 ⊔ l2) l3 (μ l1 l2 x y) z ＝ μ l1 (l2 ⊔ l3) x (μ l2 l3 y z).
```

## Definitions

```agda
record Large-Semigroup (α : Level → Level) : UUω where
  constructor
    make-Large-Semigroup
  field
    set-Large-Semigroup :
      (l : Level) → Set (α l)
    mul-Large-Semigroup :
      {l1 l2 : Level} →
      type-Set (set-Large-Semigroup l1) →
      type-Set (set-Large-Semigroup l2) →
      type-Set (set-Large-Semigroup (l1 ⊔ l2))
    associative-mul-Large-Semigroup :
      {l1 l2 l3 : Level}
      (x : type-Set (set-Large-Semigroup l1))
      (y : type-Set (set-Large-Semigroup l2))
      (z : type-Set (set-Large-Semigroup l3)) →
      mul-Large-Semigroup (mul-Large-Semigroup x y) z ＝
      mul-Large-Semigroup x (mul-Large-Semigroup y z)

open Large-Semigroup public

module _
  {α : Level → Level} (G : Large-Semigroup α)
  where

  type-Large-Semigroup : (l : Level) → UU (α l)
  type-Large-Semigroup l = type-Set (set-Large-Semigroup G l)

  is-set-type-Large-Semigroup :
    {l : Level} → is-set (type-Large-Semigroup l)
  is-set-type-Large-Semigroup = is-set-type-Set (set-Large-Semigroup G _)
```

### Small semigroups from large semigroups

```agda
module _
  {α : Level → Level} (G : Large-Semigroup α)
  where

  semigroup-Large-Semigroup : (l : Level) → Semigroup (α l)
  pr1 (semigroup-Large-Semigroup l) = set-Large-Semigroup G l
  pr1 (pr2 (semigroup-Large-Semigroup l)) = mul-Large-Semigroup G
  pr2 (pr2 (semigroup-Large-Semigroup l)) = associative-mul-Large-Semigroup G
```
