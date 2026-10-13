# Large subsemigroups

```agda
module group-theory.large-subsemigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.cumulative-large-sets
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.similarity-preserving-binary-maps-cumulative-large-sets
open import foundation.similarity-preserving-maps-cumulative-large-sets
open import foundation.universe-levels

open import group-theory.homomorphisms-large-semigroups
open import group-theory.large-semigroups
open import group-theory.semigroups
open import group-theory.subsemigroups
open import group-theory.subsets-large-semigroups
```

</details>

## Idea

A
{{#concept "subsemigroup" Disambiguation="of a large semigroup" Agda=Large-Subsemigroup}}
of a [large semigroup](group-theory.large-semigroups.md) `G` is a
[subset](group-theory.subsets-large-semigroups.md) of `G` that is closed under
multiplication.

## Definition

```agda
record
  Large-Subsemigroup
    {α : Level → Level}
    {β : Level → Level → Level}
    (γ : Level → Level)
    (G : Large-Semigroup α β) :
    UUω
  where

  field
    subset-Large-Subsemigroup : subset-Large-Semigroup γ G

    is-closed-under-mul-subset-Large-Subsemigroup :
      is-closed-under-mul-subset-Large-Semigroup
        ( G)
        ( subset-Large-Subsemigroup)

  type-Large-Subsemigroup : (l : Level) → UU (α l ⊔ γ l)
  type-Large-Subsemigroup =
    type-subset-Large-Semigroup G subset-Large-Subsemigroup

  cumulative-large-set-Large-Subsemigroup :
    Cumulative-Large-Set (λ l → α l ⊔ γ l) β
  cumulative-large-set-Large-Subsemigroup =
    cumulative-large-set-subset-Large-Semigroup G subset-Large-Subsemigroup

  inclusion-Large-Subsemigroup :
    {l : Level} → type-Large-Subsemigroup l → type-Large-Semigroup G l
  inclusion-Large-Subsemigroup = pr1

  is-in-Large-Subsemigroup :
    {l : Level} → type-Large-Semigroup G l → UU (γ l)
  is-in-Large-Subsemigroup =
    is-in-subset-Large-Semigroup G subset-Large-Subsemigroup

  prop-is-in-Large-Subsemigroup :
    {l : Level} → type-Large-Semigroup G l → Prop (γ l)
  prop-is-in-Large-Subsemigroup =
    prop-is-in-subset-Large-Semigroup G subset-Large-Subsemigroup

  abstract
    eq-type-Large-Subsemigroup :
      {l : Level} {x y : type-Large-Subsemigroup l} →
      inclusion-Large-Subsemigroup x ＝ inclusion-Large-Subsemigroup y →
      x ＝ y
    eq-type-Large-Subsemigroup =
      eq-type-subset-Large-Semigroup G subset-Large-Subsemigroup

open Large-Subsemigroup public
```

## Properties

### A large subsemigroup induces a large semigroup

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  {G : Large-Semigroup α β}
  (S : Large-Subsemigroup γ G)
  where

  mul-Large-Subsemigroup :
    {l1 l2 : Level} →
    type-Large-Subsemigroup S l1 → type-Large-Subsemigroup S l2 →
    type-Large-Subsemigroup S (l1 ⊔ l2)
  mul-Large-Subsemigroup (x , x∈S) (y , y∈S) =
    ( mul-Large-Semigroup G x y ,
      is-closed-under-mul-subset-Large-Subsemigroup S x y x∈S y∈S)

  abstract
    preserves-sim-mul-Large-Subsemigroup :
      preserves-sim-binary-operator-Cumulative-Large-Set
        ( cumulative-large-set-Large-Subsemigroup S)
        ( mul-Large-Subsemigroup)
    preserves-sim-mul-Large-Subsemigroup (x , _) (x' , _) (y , _) (y' , _) =
      preserves-sim-mul-Large-Semigroup G x x' y y'

  sim-preserving-binary-operator-mul-Large-Subsemigroup :
    sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Subsemigroup S)
  sim-preserving-binary-operator-mul-Large-Subsemigroup =
    make-sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Subsemigroup S)
      ( mul-Large-Subsemigroup)
      ( preserves-sim-mul-Large-Subsemigroup)

  abstract
    associative-mul-Large-Subsemigroup :
      {l1 l2 l3 : Level}
      (x : type-Large-Subsemigroup S l1)
      (y : type-Large-Subsemigroup S l2)
      (z : type-Large-Subsemigroup S l3) →
      mul-Large-Subsemigroup (mul-Large-Subsemigroup x y) z ＝
      mul-Large-Subsemigroup x (mul-Large-Subsemigroup y z)
    associative-mul-Large-Subsemigroup (x , _) (y , _) (z , _) =
      eq-type-Large-Subsemigroup
        ( S)
        ( associative-mul-Large-Semigroup G x y z)

  large-semigroup-Large-Subsemigroup :
    Large-Semigroup (λ l → α l ⊔ γ l) β
  large-semigroup-Large-Subsemigroup =
    make-Large-Semigroup
      ( cumulative-large-set-Large-Subsemigroup S)
      ( sim-preserving-binary-operator-mul-Large-Subsemigroup)
      ( associative-mul-Large-Subsemigroup)
```

### The inclusion homomorphism of a large subsemigroup

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  {G : Large-Semigroup α β}
  (S : Large-Subsemigroup γ G)
  where

  sim-preserving-map-inclusion-Large-Subsemigroup :
    sim-preserving-map-Cumulative-Large-Set
      ( id)
      ( cumulative-large-set-Large-Subsemigroup S)
      ( cumulative-large-set-Large-Semigroup G)
  sim-preserving-map-inclusion-Large-Subsemigroup =
    sim-preserving-map-inclusion-subset-Large-Semigroup
      ( G)
      ( subset-Large-Subsemigroup S)

  inclusion-hom-Large-Subsemigroup :
    hom-Large-Semigroup
      ( large-semigroup-Large-Subsemigroup S)
      ( G)
  inclusion-hom-Large-Subsemigroup =
    make-hom-Large-Semigroup
      ( sim-preserving-map-inclusion-Large-Subsemigroup)
      ( refl)
```

### Small subsemigroups from large subsemigroups

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  {G : Large-Semigroup α β}
  (S : Large-Subsemigroup γ G)
  where

  subsemigroup-Large-Subsemigroup :
    (l : Level) → Subsemigroup (γ l) (semigroup-Large-Semigroup G l)
  subsemigroup-Large-Subsemigroup l =
    ( prop-is-in-Large-Subsemigroup S ,
      is-closed-under-mul-subset-Large-Subsemigroup S _ _)
```
