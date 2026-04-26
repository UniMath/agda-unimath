# Set-magmoids

```agda
module category-theory.set-magmoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "set-magmoid" Agda=Set-Magmoid}} is the
[structure](foundation.structure.md) of a
[composition operation on a binary family of sets](category-theory.composition-operations-on-binary-families-of-sets.md),
and are the _oidification_ of [magmas](structured-types.magmas.md) in
[sets](foundation-core.sets.md) in one sense of the term. We call elements of
the indexing type **objects**, and elements of the set-family **morphisms** or
**homomorphisms**.

Set-magmoids serve as our starting point in the study of the
[structure](foundation.structure.md) of
[categories](category-theory.categories.md). Indeed, categories form a
[subtype](foundation-core.subtypes.md) of set-magmoids, although
structure-preserving maps of set-magmoids do not automatically preserve identity
morphisms.

Set-magmoids are commonly referred to as _magmoids_ in the literature, but we
use the "set-" prefix to make clear its relation to magmas. Set-magmoids should
not be confused with _strict_ magmoids, which would be set-magmoids whose
objects form a set.

## Definitions

### The type of set-magmoids

```agda
Set-Magmoid :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Set-Magmoid l1 l2 =
  Σ ( UU l1)
    ( λ A →
      Σ ( A → A → Set l2)
        ( composition-operation-binary-family-Set))

module _
  {l1 l2 : Level} (M : Set-Magmoid l1 l2)
  where

  obj-Set-Magmoid : UU l1
  obj-Set-Magmoid = pr1 M

  hom-set-Set-Magmoid : (x y : obj-Set-Magmoid) → Set l2
  hom-set-Set-Magmoid = pr1 (pr2 M)

  hom-Set-Magmoid : (x y : obj-Set-Magmoid) → UU l2
  hom-Set-Magmoid x y = type-Set (hom-set-Set-Magmoid x y)

  is-set-hom-Set-Magmoid :
    (x y : obj-Set-Magmoid) → is-set (hom-Set-Magmoid x y)
  is-set-hom-Set-Magmoid x y =
    is-set-type-Set (hom-set-Set-Magmoid x y)

  comp-hom-Set-Magmoid :
    {x y z : obj-Set-Magmoid} →
    hom-Set-Magmoid y z →
    hom-Set-Magmoid x y →
    hom-Set-Magmoid x z
  comp-hom-Set-Magmoid = pr2 (pr2 M)

  comp-hom-Set-Magmoid' :
    {x y z : obj-Set-Magmoid} →
    hom-Set-Magmoid x y →
    hom-Set-Magmoid y z →
    hom-Set-Magmoid x z
  comp-hom-Set-Magmoid' f g = comp-hom-Set-Magmoid g f
```

### The total hom-type of a set-magmoid

```agda
total-hom-Set-Magmoid :
  {l1 l2 : Level} (M : Set-Magmoid l1 l2) → UU (l1 ⊔ l2)
total-hom-Set-Magmoid M =
  Σ ( obj-Set-Magmoid M)
    ( λ x → Σ (obj-Set-Magmoid M) (hom-Set-Magmoid M x))

obj-total-hom-Set-Magmoid :
  {l1 l2 : Level} (M : Set-Magmoid l1 l2) →
  total-hom-Set-Magmoid M → obj-Set-Magmoid M × obj-Set-Magmoid M
pr1 (obj-total-hom-Set-Magmoid M (x , y , f)) = x
pr2 (obj-total-hom-Set-Magmoid M (x , y , f)) = y
```

### Pre- and postcomposition by a morphism

```agda
module _
  {l1 l2 : Level} (M : Set-Magmoid l1 l2)
  {x y : obj-Set-Magmoid M}
  (f : hom-Set-Magmoid M x y)
  (z : obj-Set-Magmoid M)
  where

  precomp-hom-Set-Magmoid : hom-Set-Magmoid M y z → hom-Set-Magmoid M x z
  precomp-hom-Set-Magmoid g = comp-hom-Set-Magmoid M g f

  postcomp-hom-Set-Magmoid : hom-Set-Magmoid M z x → hom-Set-Magmoid M z y
  postcomp-hom-Set-Magmoid = comp-hom-Set-Magmoid M f
```

### The predicate on set-magmoids of being associative

```agda
module _
  {l1 l2 : Level} (M : Set-Magmoid l1 l2)
  where

  is-associative-Set-Magmoid : UU (l1 ⊔ l2)
  is-associative-Set-Magmoid =
    is-associative-composition-operation-binary-family-Set
      ( hom-set-Set-Magmoid M)
      ( comp-hom-Set-Magmoid M)

  is-prop-is-associative-Set-Magmoid :
    is-prop
      ( is-associative-composition-operation-binary-family-Set
        ( hom-set-Set-Magmoid M)
        ( comp-hom-Set-Magmoid M))
  is-prop-is-associative-Set-Magmoid =
    is-prop-is-associative-composition-operation-binary-family-Set
      ( hom-set-Set-Magmoid M)
      ( comp-hom-Set-Magmoid M)

  is-associative-prop-Set-Magmoid : Prop (l1 ⊔ l2)
  is-associative-prop-Set-Magmoid =
    is-associative-prop-composition-operation-binary-family-Set
      ( hom-set-Set-Magmoid M)
      ( comp-hom-Set-Magmoid M)
```

### The predicate on set-magmoids of being unital

**Proof:** To show that unitality is a proposition, suppose
`e e' : (x : A) → hom x x` are both two-sided units with respect to composition.
It is enough to show that `e ＝ e'` since the right and left unit laws are
propositions by the set-condition on hom-types. By function extensionality, it
is enough to show that `e x ＝ e' x` for all `x : A`, and by the unit laws we
have:

```text
  e x ＝ (e' x) ∘ (e x) ＝ e' x. ∎
```

```agda
module _
  {l1 l2 : Level} (M : Set-Magmoid l1 l2)
  where

  is-unital-Set-Magmoid : UU (l1 ⊔ l2)
  is-unital-Set-Magmoid =
    is-unital-composition-operation-binary-family-Set
      ( hom-set-Set-Magmoid M)
      ( comp-hom-Set-Magmoid M)

  is-prop-is-unital-Set-Magmoid :
    is-prop
      ( is-unital-composition-operation-binary-family-Set
        ( hom-set-Set-Magmoid M)
        ( comp-hom-Set-Magmoid M))
  is-prop-is-unital-Set-Magmoid =
    is-prop-is-unital-composition-operation-binary-family-Set
      ( hom-set-Set-Magmoid M)
      ( comp-hom-Set-Magmoid M)

  is-unital-prop-Set-Magmoid : Prop (l1 ⊔ l2)
  is-unital-prop-Set-Magmoid =
    is-unital-prop-composition-operation-binary-family-Set
      ( hom-set-Set-Magmoid M)
      ( comp-hom-Set-Magmoid M)
```

## Properties

### If the objects of a set-magmoid are `k`-truncated for nonnegative `k`, the total hom-type is `k`-truncated

```agda
module _
  {l1 l2 : Level} {k : 𝕋} (M : Set-Magmoid l1 l2)
  where

  is-trunc-total-hom-is-trunc-obj-Set-Magmoid :
    is-trunc (succ-𝕋 (succ-𝕋 k)) (obj-Set-Magmoid M) →
    is-trunc (succ-𝕋 (succ-𝕋 k)) (total-hom-Set-Magmoid M)
  is-trunc-total-hom-is-trunc-obj-Set-Magmoid is-trunc-obj-M =
    is-trunc-Σ
      ( is-trunc-obj-M)
      ( λ x →
        is-trunc-Σ
          ( is-trunc-obj-M)
          ( λ y → is-trunc-is-set k (is-set-hom-Set-Magmoid M x y)))

  total-hom-truncated-type-is-trunc-obj-Set-Magmoid :
    is-trunc (succ-𝕋 (succ-𝕋 k)) (obj-Set-Magmoid M) →
    Truncated-Type (l1 ⊔ l2) (succ-𝕋 (succ-𝕋 k))
  pr1 (total-hom-truncated-type-is-trunc-obj-Set-Magmoid is-trunc-obj-M) =
    total-hom-Set-Magmoid M
  pr2 (total-hom-truncated-type-is-trunc-obj-Set-Magmoid is-trunc-obj-M) =
    is-trunc-total-hom-is-trunc-obj-Set-Magmoid is-trunc-obj-M
```

## See also

- [Magmas](structured-types.magmas.md) are types equipped with a binary
  operation.
- [Nonunital precategories](category-theory.nonunital-precategories.md) are
  associative set-magmoids.
- [Precategories](category-theory.precategories.md) are associative and unital
  set-magmoids.
- [Categories](category-theory.categories.md) are univalent, associative and
  unital set-magmoids.
- [Strict categories](category-theory.categories.md) are associative and unital
  set-magmoids whose objects form a set.

## External links

- [magmoid](https://ncatlab.org/nlab/show/magmoid) at $n$Lab

A wikidata identifier was not available for this concept.
