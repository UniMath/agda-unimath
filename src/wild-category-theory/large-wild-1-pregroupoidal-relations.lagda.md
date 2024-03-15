# Large wild 1-pregroupoidal relations

```agda
module wild-category-theory.large-wild-1-pregroupoidal-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.large-binary-relations
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.reflexive-relations
open import foundation.strictly-right-unital-concatenation-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.propositions
```

</details>

## Idea

A {{#concept "large wild 1-pregroupoidal relation" }} `R` on a type `A` is a
wild [equivalence relation](foundation.equivalence-relations.md) on `A` in the
sense that the relation is not required to be valued in
[propositions](foundation-core.propositions.md).

## Definitions

### The structure of a large wild 1-pregroupoid on a large relation

```agda
record
  is-large-wild-1-pregroupoid
  {α : Level → Level} {β : Level → Level → Level}
  {A : (l : Level) → UU (α l)}
  (R : Large-Relation α β A)
  : UUω
  where

  field
    is-large-reflexive-is-large-wild-1-pregroupoid :
      is-reflexive-Large-Relation R

  -- is-reflexive R × is-symmetric R × is-transitive R

-- module _
--   {l1 l2 : Level} {A : UU l1} {R : Relation l2 A}
--   (H : is-wild-1-pregroupoid R)
--   where

--   reflexive-is-wild-1-pregroupoid : is-reflexive R
--   reflexive-is-wild-1-pregroupoid = pr1 H

--   refl-is-wild-1-pregroupoid :
--     {x : A} → R x x
--   refl-is-wild-1-pregroupoid {x} =
--     reflexive-is-wild-1-pregroupoid x

--   symmetric-is-wild-1-pregroupoid : is-symmetric R
--   symmetric-is-wild-1-pregroupoid = pr1 (pr2 H)

--   inv-is-wild-1-pregroupoid :
--     {x y : A} → R x y → R y x
--   inv-is-wild-1-pregroupoid {x} {y} =
--     symmetric-is-wild-1-pregroupoid x y

--   transitive-is-wild-1-pregroupoid : is-transitive R
--   transitive-is-wild-1-pregroupoid = pr2 (pr2 H)

--   comp-is-wild-1-pregroupoid :
--     {x y z : A} → R y z → R x y → R x z
--   comp-is-wild-1-pregroupoid {x} {y} {z} =
--     transitive-is-wild-1-pregroupoid x y z
```

### The type of wild equivalence relations

```text
Wild-1-Pregroupoid-Relation :
  (l : Level) {l1 : Level} (A : UU l1) → UU ((lsuc l) ⊔ l1)
Wild-1-Pregroupoid-Relation l A = Σ (Relation l A) is-wild-1-pregroupoid

module _
  {l1 l2 : Level} {A : UU l1} (R : Wild-1-Pregroupoid-Relation l2 A)
  where

  sim-Wild-1-Pregroupoid-Relation : Relation l2 A
  sim-Wild-1-Pregroupoid-Relation = pr1 R

  is-wild-1-pregroupoid-sim-Wild-1-Pregroupoid-Relation :
    is-wild-1-pregroupoid sim-Wild-1-Pregroupoid-Relation
  is-wild-1-pregroupoid-sim-Wild-1-Pregroupoid-Relation = pr2 R

  reflexive-Wild-1-Pregroupoid-Relation :
    is-reflexive sim-Wild-1-Pregroupoid-Relation
  reflexive-Wild-1-Pregroupoid-Relation =
    reflexive-is-wild-1-pregroupoid
      ( is-wild-1-pregroupoid-sim-Wild-1-Pregroupoid-Relation)

  refl-Wild-1-Pregroupoid-Relation :
    {x : A} → sim-Wild-1-Pregroupoid-Relation x x
  refl-Wild-1-Pregroupoid-Relation {x} =
    reflexive-Wild-1-Pregroupoid-Relation x

  symmetric-Wild-1-Pregroupoid-Relation :
    is-symmetric sim-Wild-1-Pregroupoid-Relation
  symmetric-Wild-1-Pregroupoid-Relation =
    symmetric-is-wild-1-pregroupoid
      ( is-wild-1-pregroupoid-sim-Wild-1-Pregroupoid-Relation)

  inv-Wild-1-Pregroupoid-Relation :
    {x y : A} →
    sim-Wild-1-Pregroupoid-Relation x y → sim-Wild-1-Pregroupoid-Relation y x
  inv-Wild-1-Pregroupoid-Relation {x} {y} =
    symmetric-Wild-1-Pregroupoid-Relation x y

  transitive-Wild-1-Pregroupoid-Relation :
    is-transitive sim-Wild-1-Pregroupoid-Relation
  transitive-Wild-1-Pregroupoid-Relation =
    transitive-is-wild-1-pregroupoid
      ( is-wild-1-pregroupoid-sim-Wild-1-Pregroupoid-Relation)

  comp-Wild-1-Pregroupoid-Relation :
    {x y z : A} →
    sim-Wild-1-Pregroupoid-Relation y z →
    sim-Wild-1-Pregroupoid-Relation x y →
    sim-Wild-1-Pregroupoid-Relation x z
  comp-Wild-1-Pregroupoid-Relation {x} {y} {z} =
    transitive-Wild-1-Pregroupoid-Relation
      ( x)
      ( y)
      ( z)
```

## Properties

### Symmetry induces logical equivalences `R(x,y) ↔ R(y,x)`

```text
iff-inv-Wild-1-Pregroupoid-Relation :
  {l1 l2 : Level} {A : UU l1} (R : Wild-1-Pregroupoid-Relation l2 A) {x y : A} →
  sim-Wild-1-Pregroupoid-Relation R x y ↔ sim-Wild-1-Pregroupoid-Relation R y x
pr1 (iff-inv-Wild-1-Pregroupoid-Relation R) =
  inv-Wild-1-Pregroupoid-Relation R
pr2 (iff-inv-Wild-1-Pregroupoid-Relation R) =
  inv-Wild-1-Pregroupoid-Relation R
```

### Transitivity induces logical equivalences `R(y,z) ↔ R(x,z)`

```text
iff-comp-Wild-1-Pregroupoid-Relation :
  {l1 l2 : Level} {A : UU l1}
  (R : Wild-1-Pregroupoid-Relation l2 A) {x y z : A} →
  sim-Wild-1-Pregroupoid-Relation R x y →
  sim-Wild-1-Pregroupoid-Relation R y z ↔ sim-Wild-1-Pregroupoid-Relation R x z
pr1 (iff-comp-Wild-1-Pregroupoid-Relation R r) s =
  comp-Wild-1-Pregroupoid-Relation R s r
pr2 (iff-comp-Wild-1-Pregroupoid-Relation R r) s =
  comp-Wild-1-Pregroupoid-Relation R
    ( s)
    ( inv-Wild-1-Pregroupoid-Relation R r)
```

### Transitivity induces logical equivalences `R(x,y) ↔ R(x,z)`

```text
iff-comp-Wild-1-Pregroupoid-Relation' :
  {l1 l2 : Level} {A : UU l1}
  (R : Wild-1-Pregroupoid-Relation l2 A) {x y z : A} →
  sim-Wild-1-Pregroupoid-Relation R y z →
  sim-Wild-1-Pregroupoid-Relation R x y ↔ sim-Wild-1-Pregroupoid-Relation R x z
pr1 (iff-comp-Wild-1-Pregroupoid-Relation' R r) =
  comp-Wild-1-Pregroupoid-Relation R r
pr2 (iff-comp-Wild-1-Pregroupoid-Relation' R r) =
  comp-Wild-1-Pregroupoid-Relation R (inv-Wild-1-Pregroupoid-Relation R r)
```

## Examples

### Equivalence relations are wild 1-pregroupoids

```text
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-wild-1-pregroupoid-equivalence-relation :
    is-wild-1-pregroupoid (sim-equivalence-relation R)
  is-wild-1-pregroupoid-equivalence-relation = pr2 R

  wild-1-pregroupoid-equivalence-relation :
    Wild-1-Pregroupoid-Relation l2 A
  pr1 wild-1-pregroupoid-equivalence-relation =
    sim-equivalence-relation R
  pr2 wild-1-pregroupoid-equivalence-relation =
    is-wild-1-pregroupoid-equivalence-relation
```

### The indiscrete wild equivalence relation on a type

```text
indiscrete-Wild-1-Pregroupoid-Relation :
  {l1 : Level} (A : UU l1) → Wild-1-Pregroupoid-Relation lzero A
indiscrete-Wild-1-Pregroupoid-Relation A =
  wild-1-pregroupoid-equivalence-relation
    ( indiscrete-equivalence-relation A)
```

### The wild equivalence relation of identities on a type

This can also be called the _discrete_ wild equivalence relation.

```text
module _
  {l1 : Level} (A : UU l1)
  where

  is-wild-1-pregroupoid-Id :
    is-wild-1-pregroupoid (Id {A = A})
  pr1 is-wild-1-pregroupoid-Id _ = refl
  pr1 (pr2 is-wild-1-pregroupoid-Id) _ _ = inv
  pr2 (pr2 is-wild-1-pregroupoid-Id) _ _ _ p q = q ∙ᵣ p

  Id-Wild-1-Pregroupoid-Relation :
    Wild-1-Pregroupoid-Relation l1 A
  pr1 Id-Wild-1-Pregroupoid-Relation = Id
  pr2 Id-Wild-1-Pregroupoid-Relation = is-wild-1-pregroupoid-Id
```

**Note.** We intentionally define the transitivity operation via the strictly
right unital concatenation operation, as this makes the strict symmetrization
strictly left unital.

### The wild equivalence relation of homotopies on a function type

```text
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  is-wild-1-pregroupoid-htpy :
    is-wild-1-pregroupoid (_~_ {B = B})
  pr1 is-wild-1-pregroupoid-htpy _ = refl-htpy
  pr1 (pr2 is-wild-1-pregroupoid-htpy) _ _ = inv-htpy
  pr2 (pr2 is-wild-1-pregroupoid-htpy) _ _ _ p q x = q x ∙ᵣ p x

  htpy-Wild-1-Pregroupoid-Relation :
    Wild-1-Pregroupoid-Relation (l1 ⊔ l2) ((x : A) → B x)
  pr1 htpy-Wild-1-Pregroupoid-Relation = _~_
  pr2 htpy-Wild-1-Pregroupoid-Relation = is-wild-1-pregroupoid-htpy
```

### The wild equivalence relation of equivalences in a universe

```text
module _
  {l : Level}
  where

  is-wild-1-pregroupoid-equiv-UU :
    is-wild-1-pregroupoid (_≃_ {l} {l})
  pr1 is-wild-1-pregroupoid-equiv-UU _ = id-equiv
  pr1 (pr2 is-wild-1-pregroupoid-equiv-UU) _ _ = inv-equiv
  pr2 (pr2 is-wild-1-pregroupoid-equiv-UU) _ _ _ = _∘e_

  equiv-UU-Wild-1-Pregroupoid-Relation :
    Wild-1-Pregroupoid-Relation l (UU l)
  pr1 equiv-UU-Wild-1-Pregroupoid-Relation = _≃_
  pr2 equiv-UU-Wild-1-Pregroupoid-Relation = is-wild-1-pregroupoid-equiv-UU
```

## References

- HoTT, _Coq-HoTT_/`theories/WildCat/Core.v`, file in GitHub repository
  (<https://github.com/HoTT/Coq-HoTT/blob/master/theories/WildCat/Core.v>)
