# Large abelian groups

```agda
module group-theory.large-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.logical-equivalences
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.large-commutative-monoids
open import group-theory.large-groups
open import group-theory.large-monoids
```

</details>

## Idea

A {{#concept "large abelian group" Agda=Large-Ab}} is a
[large group](group-theory.large-groups.md) whose binary operation is
commutative.

## Definition

```agda
record Large-Ab (α : Level → Level) (β : Level → Level → Level) : UUω where

  constructor
    make-Large-Ab

  field
    large-group-Large-Ab : Large-Group α β

  type-Large-Ab : (l : Level) → UU (α l)
  type-Large-Ab = type-Large-Group large-group-Large-Ab

  set-Large-Ab : (l : Level) → Set (α l)
  set-Large-Ab = set-Large-Group large-group-Large-Ab

  add-Large-Ab :
    {l1 l2 : Level} → type-Large-Ab l1 → type-Large-Ab l2 →
    type-Large-Ab (l1 ⊔ l2)
  add-Large-Ab = mul-Large-Group large-group-Large-Ab

  zero-Large-Ab : type-Large-Ab lzero
  zero-Large-Ab = unit-Large-Group large-group-Large-Ab

  neg-Large-Ab : {l : Level} → type-Large-Ab l → type-Large-Ab l
  neg-Large-Ab = inv-Large-Group large-group-Large-Ab

  field
    commutative-add-Large-Ab :
      {l1 l2 : Level} → (x : type-Large-Ab l1) → (y : type-Large-Ab l2) →
      add-Large-Ab x y ＝ add-Large-Ab y x

open Large-Ab public
```

## Properties

### The similarity relation of a large abelian group

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  sim-prop-Large-Ab : Large-Relation-Prop β (type-Large-Ab G)
  sim-prop-Large-Ab = sim-prop-Large-Group (large-group-Large-Ab G)

  sim-Large-Ab : Large-Relation β (type-Large-Ab G)
  sim-Large-Ab = sim-Large-Group (large-group-Large-Ab G)

  refl-sim-Large-Ab :
    {l : Level} (x : type-Large-Ab G l) → sim-Large-Ab x x
  refl-sim-Large-Ab = refl-sim-Large-Group (large-group-Large-Ab G)

  symmetric-sim-Large-Ab :
    {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
    sim-Large-Ab x y → sim-Large-Ab y x
  symmetric-sim-Large-Ab = symmetric-sim-Large-Group (large-group-Large-Ab G)

  transitive-sim-Large-Ab :
    {l1 l2 l3 : Level} →
    (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) (z : type-Large-Ab G l3) →
    sim-Large-Ab y z → sim-Large-Ab x y → sim-Large-Ab x z
  transitive-sim-Large-Ab =
    transitive-sim-Large-Group (large-group-Large-Ab G)
```

### Raising universe levels

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (G : Large-Ab α β)
  where

  raise-Large-Ab :
    {l1 : Level} (l2 : Level) (x : type-Large-Ab G l1) →
    type-Large-Ab G (l1 ⊔ l2)
  raise-Large-Ab = raise-Large-Group (large-group-Large-Ab G)

  raise-zero-Large-Ab : (l : Level) → type-Large-Ab G l
  raise-zero-Large-Ab = raise-unit-Large-Group (large-group-Large-Ab G)

  sim-raise-Large-Ab :
    {l1 : Level} (l2 : Level) (x : type-Large-Ab G l1) →
    sim-Large-Ab G x (raise-Large-Ab l2 x)
  sim-raise-Large-Ab = sim-raise-Large-Group (large-group-Large-Ab G)

  sim-raise-Large-Ab' :
    {l1 : Level} (l2 : Level) (x : type-Large-Ab G l1) →
    sim-Large-Ab G (raise-Large-Ab l2 x) x
  sim-raise-Large-Ab' = sim-raise-Large-Group' (large-group-Large-Ab G)

  eq-raise-Large-Ab :
    (l1 : Level) {l2 : Level} (x : type-Large-Ab G (l1 ⊔ l2)) →
    raise-Large-Ab l2 x ＝ x
  eq-raise-Large-Ab = eq-raise-Large-Group (large-group-Large-Ab G)

  raise-raise-Large-Ab :
    {l1 l2 l3 : Level} → (x : type-Large-Ab G l1) →
    raise-Large-Ab l2 (raise-Large-Ab l3 x) ＝
    raise-Large-Ab (l2 ⊔ l3) x
  raise-raise-Large-Ab = raise-raise-Large-Group (large-group-Large-Ab G)

  raise-left-add-Large-Ab :
    {l1 l2 l3 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
    add-Large-Ab G (raise-Large-Ab l3 x) y ＝
    raise-Large-Ab l3 (add-Large-Ab G x y)
  raise-left-add-Large-Ab = raise-left-mul-Large-Group (large-group-Large-Ab G)

  raise-right-add-Large-Ab :
    {l1 l2 l3 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
    add-Large-Ab G x (raise-Large-Ab l3 y) ＝
    raise-Large-Ab l3 (add-Large-Ab G x y)
  raise-right-add-Large-Ab =
    raise-right-mul-Large-Group (large-group-Large-Ab G)

  raise-left-unit-law-Large-Ab :
    {l1 l2 : Level} (x : type-Large-Ab G l1) →
    add-Large-Ab G (raise-zero-Large-Ab l2) x ＝ raise-Large-Ab l2 x
  raise-left-unit-law-Large-Ab =
    raise-left-unit-law-Large-Group (large-group-Large-Ab G)

  raise-right-unit-law-Large-Ab :
    {l1 l2 : Level} (x : type-Large-Ab G l1) →
    add-Large-Ab G x (raise-zero-Large-Ab l2) ＝
    raise-Large-Ab l2 x
  raise-right-unit-law-Large-Ab =
    raise-right-unit-law-Large-Group (large-group-Large-Ab G)

  raise-unit-lzero-Large-Ab :
    raise-zero-Large-Ab lzero ＝ zero-Large-Ab G
  raise-unit-lzero-Large-Ab =
    raise-unit-lzero-Large-Group (large-group-Large-Ab G)
```

### The negative of the identity is the identity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    neg-zero-Large-Ab : neg-Large-Ab G (zero-Large-Ab G) ＝ zero-Large-Ab G
    neg-zero-Large-Ab = inv-unit-Large-Group (large-group-Large-Ab G)
```

### Uniqueness of additive right inverses

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    unique-right-neg-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      (add-Large-Ab G x y ＝ raise-zero-Large-Ab G (l1 ⊔ l2)) →
      sim-Large-Ab G y (neg-Large-Ab G x)
    unique-right-neg-Large-Ab =
      unique-right-inv-Large-Group (large-group-Large-Ab G)
```

### Uniqueness of additive left inverses

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    unique-left-neg-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      (add-Large-Ab G x y ＝ raise-zero-Large-Ab G (l1 ⊔ l2)) →
      sim-Large-Ab G x (neg-Large-Ab G y)
    unique-left-neg-Large-Ab =
      unique-left-inv-Large-Group (large-group-Large-Ab G)
```

### Distributivity of negation over addition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    distributive-neg-add-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      neg-Large-Ab G (add-Large-Ab G x y) ＝
      add-Large-Ab G (neg-Large-Ab G x) (neg-Large-Ab G y)
    distributive-neg-add-Large-Ab x y =
      ( distributive-inv-mul-Large-Group (large-group-Large-Ab G) x y) ∙
      ( commutative-add-Large-Ab G _ _)
```

### Negation is an involution

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    neg-neg-Large-Ab :
      {l : Level} (x : type-Large-Ab G l) →
      neg-Large-Ab G (neg-Large-Ab G x) ＝ x
    neg-neg-Large-Ab = inv-inv-Large-Group (large-group-Large-Ab G)

  aut-neg-Large-Ab : (l : Level) → Aut (type-Large-Ab G l)
  aut-neg-Large-Ab = aut-inv-Large-Group (large-group-Large-Ab G)
```

### The raise operation characterizes the similarity relation

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  sim-iff-eq-raise-Large-Ab :
    {l1 l2 : Level} →
    (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
    ( sim-Large-Ab G x y) ↔
    ( raise-Large-Ab G l2 x ＝ raise-Large-Ab G l1 y)
  sim-iff-eq-raise-Large-Ab =
    sim-iff-eq-raise-Large-Group (large-group-Large-Ab G)

  sim-eq-raise-Large-Ab :
    {l1 l2 : Level} →
    (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
    (raise-Large-Ab G l2 x ＝ raise-Large-Ab G l1 y) →
    sim-Large-Ab G x y
  sim-eq-raise-Large-Ab x y =
    backward-implication (sim-iff-eq-raise-Large-Ab x y)

  eq-raise-sim-Large-Ab :
    {l1 l2 : Level} →
    (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
    sim-Large-Ab G x y →
    raise-Large-Ab G l2 x ＝ raise-Large-Ab G l1 y
  eq-raise-sim-Large-Ab x y =
    forward-implication (sim-iff-eq-raise-Large-Ab x y)
```

### Small abelian groups from large abelian groups

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  group-Large-Ab : (l : Level) → Group (α l)
  group-Large-Ab = group-Large-Group (large-group-Large-Ab G)

  ab-Large-Ab : (l : Level) → Ab (α l)
  ab-Large-Ab l =
    ( group-Large-Ab l ,
      commutative-add-Large-Ab G)
```

### Large commutative monoids from large abelian groups

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  large-monoid-Large-Ab : Large-Monoid α β
  large-monoid-Large-Ab = large-monoid-Large-Group (large-group-Large-Ab G)

  large-commutative-monoid-Large-Ab : Large-Commutative-Monoid α β
  large-commutative-monoid-Large-Ab =
    make-Large-Commutative-Monoid
      ( large-monoid-Large-Ab)
      ( commutative-add-Large-Ab G)
```

### Cancellation laws in a large abelian group

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    cancel-left-diff-add-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      add-Large-Ab G (neg-Large-Ab G x) (add-Large-Ab G x y) ＝
      raise-Large-Ab G l1 y
    cancel-left-diff-add-Large-Ab =
      cancel-left-div-mul-Large-Group (large-group-Large-Ab G)

    sim-cancel-left-diff-add-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      sim-Large-Ab G
        ( add-Large-Ab G (neg-Large-Ab G x) (add-Large-Ab G x y))
        ( y)
    sim-cancel-left-diff-add-Large-Ab =
      sim-cancel-left-div-mul-Large-Group (large-group-Large-Ab G)

    cancel-left-add-diff-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      add-Large-Ab G x (add-Large-Ab G (neg-Large-Ab G x) y) ＝
      raise-Large-Ab G l1 y
    cancel-left-add-diff-Large-Ab =
      cancel-left-mul-div-Large-Group (large-group-Large-Ab G)

    sim-cancel-left-add-diff-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      sim-Large-Ab G
        ( add-Large-Ab G x (add-Large-Ab G (neg-Large-Ab G x) y))
        ( y)
    sim-cancel-left-add-diff-Large-Ab =
      sim-cancel-left-mul-div-Large-Group (large-group-Large-Ab G)

    cancel-right-add-diff-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      add-Large-Ab G (add-Large-Ab G y x) (neg-Large-Ab G x) ＝
      raise-Large-Ab G l1 y
    cancel-right-add-diff-Large-Ab =
      cancel-right-mul-div-Large-Group (large-group-Large-Ab G)

    sim-cancel-right-add-diff-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      sim-Large-Ab G
        ( add-Large-Ab G (add-Large-Ab G y x) (neg-Large-Ab G x))
        ( y)
    sim-cancel-right-add-diff-Large-Ab =
      sim-cancel-right-mul-div-Large-Group (large-group-Large-Ab G)

    cancel-right-diff-add-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      add-Large-Ab G (add-Large-Ab G y (neg-Large-Ab G x)) x ＝
      raise-Large-Ab G l1 y
    cancel-right-diff-add-Large-Ab =
      cancel-right-div-mul-Large-Group (large-group-Large-Ab G)

    sim-cancel-right-diff-add-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      sim-Large-Ab G
        ( add-Large-Ab G (add-Large-Ab G y (neg-Large-Ab G x)) x)
        ( y)
    sim-cancel-right-diff-add-Large-Ab =
      sim-cancel-right-div-mul-Large-Group (large-group-Large-Ab G)
```

### Addition by an element of a large abelian group is an embedding

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  {l1 : Level} (l2 : Level) (x : type-Large-Ab G l1)
  where

  emb-left-add-Large-Ab : type-Large-Ab G l2 ↪ type-Large-Ab G (l1 ⊔ l2)
  emb-left-add-Large-Ab = emb-left-mul-Large-Group (large-group-Large-Ab G) l2 x

  emb-right-add-Large-Ab : type-Large-Ab G l2 ↪ type-Large-Ab G (l1 ⊔ l2)
  emb-right-add-Large-Ab =
    emb-right-mul-Large-Group (large-group-Large-Ab G) l2 x
```
