# Contratransitive binary relations

```agda
module foundation.contratransitive-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.iterated-dependent-product-types
open import foundation.reflexive-relations
open import foundation.transitive-binary-relations
open import foundation.universe-levels

open import foundation-core.propositions
```

</details>

## Idea

A
{{#concept "left contratransitive binary relation" Agda=is-left-contratransitive Agda=Right-Contratransitive-Relation}}
is a [relation](foundation.binary-relations.md) `R` on `A` such that for every
triple `x y z : A`, there is a binary operation

```text
  R x z → R y z → R x y.
```

Contratransitive binary relations are closely related to
[transitive relations](foundation.transitive-binary-relations.md), but have a
sort of mixed variance.

Instead of giving, for every diagram

```text
        y
       ∧ \
     /    \
    /      ∨
  x         z
```

a horizontal arrow

```text
        y
       ∧ \
     /    \
    /      ∨
  x ⋯⋯⋯⋯⋯⋯> z,
```

a contratransitive binary relation gives, for every cospan

```text
        y
         \
          \
           ∨
  x ------> z
```

a lift

```text
        y
       ∧ \
     ⋰    \
   ⋰       ∨
  x ------> z.
```

Note that by symmetry it also gives a lift in the opposite direction

```text
        y
      ⋰  \
    ⋰     \
   ∨        ∨
  x ------> z.
```

Similarly, a
{{#concept "right contratransitive binary relation" Agda=is-right-contratransitive Agda=Right-Contratransitive-Relation}}
is a relation `R` on `A` such that for every triple `x y z : A`, there is a
binary operation

```text
  R x y → R x z → R y z.
```

## Definition

### The structure of being a contratransitive relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where


  is-left-contratransitive : UU (l1 ⊔ l2)
  is-left-contratransitive = {x y z : A} → R x z → R y z → R x y

  is-right-contratransitive : UU (l1 ⊔ l2)
  is-right-contratransitive = {x y z : A} → R x y → R x z → R y z
```

### The predicate of being a contratransitive relation valued in propositions

A relation `R` on a type `A` valued in propositions is said to be
{{#concept "(left/right) contratransitive" Disambiguation="relation valued in propositions" Agda=is-right-contratransitive-Relation-Prop}}
if its underlying relation is (left/right) contratransitive.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  where

  is-right-contratransitive-Relation-Prop : UU (l1 ⊔ l2)
  is-right-contratransitive-Relation-Prop = is-right-contratransitive (type-Relation-Prop R)

  is-prop-is-right-contratransitive-Relation-Prop :
    is-prop is-right-contratransitive-Relation-Prop
  is-prop-is-right-contratransitive-Relation-Prop =
    is-prop-iterated-implicit-Π 3
      ( λ x y z →
        is-prop-function-type
          ( is-prop-function-type (is-prop-type-Relation-Prop R y z)))
```

### The type of contratransitive relations

```agda
Right-Contratransitive-Relation :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Right-Contratransitive-Relation l2 A =
  Σ (Relation l2 A) (is-right-contratransitive)

module _
  {l1 l2 : Level} {A : UU l1} (R : Right-Contratransitive-Relation l2 A)
  where

  rel-Right-Contratransitive-Relation : Relation l2 A
  rel-Right-Contratransitive-Relation = pr1 R

  is-right-contratransitive-rel-Right-Contratransitive-Relation :
    is-right-contratransitive rel-Right-Contratransitive-Relation
  is-right-contratransitive-rel-Right-Contratransitive-Relation = pr2 R
```

### The type of contratransitive relations valued in propositions

```agda
Right-Contratransitive-Relation-Prop :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Right-Contratransitive-Relation-Prop l2 A =
  Σ (Relation-Prop l2 A) (is-right-contratransitive-Relation-Prop)

module _
  {l1 l2 : Level} {A : UU l1} (R : Right-Contratransitive-Relation-Prop l2 A)
  where

  rel-prop-Right-Contratransitive-Relation-Prop : Relation-Prop l2 A
  rel-prop-Right-Contratransitive-Relation-Prop = pr1 R

  rel-Right-Contratransitive-Relation-Prop : Relation l2 A
  rel-Right-Contratransitive-Relation-Prop =
    type-Relation-Prop rel-prop-Right-Contratransitive-Relation-Prop

  is-right-contratransitive-rel-Right-Contratransitive-Relation-Prop :
    is-right-contratransitive rel-Right-Contratransitive-Relation-Prop
  is-right-contratransitive-rel-Right-Contratransitive-Relation-Prop = pr2 R
```

## Properties

### If there is an element that relates to `y` then `y` relates to `y`

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  leq-self-any-leq-is-right-contratransitive :
    is-right-contratransitive R → {x y : A} → R x y → R y y
  leq-self-any-leq-is-right-contratransitive H p = H p p
```

### The reverse element related to a contratransitivity element

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  reverse-is-right-contratransitive :
    is-right-contratransitive R → {x y z : A} → R z x → R z y → R y x
  reverse-is-right-contratransitive H p q = H q p
```

### Contratransitive and reflexive relations are symmetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  (H : is-right-contratransitive R)
  where

  is-symmetric-is-reflexive-is-right-contratransitive-Relation :
    is-reflexive R → is-symmetric R
  is-symmetric-is-reflexive-is-right-contratransitive-Relation r x y p =
    H p (r x)
```

### Contratransitive and reflexive relations satisfy all 2-horn filler conditions

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  (H : is-right-contratransitive R)
  where

  is-transitive-is-symmetric-is-right-contratransitive-Relation :
    is-symmetric R → is-transitive R
  is-transitive-is-symmetric-is-right-contratransitive-Relation s x y z p q =
    H (s x y q) p

  is-transitive-is-reflexive-is-right-contratransitive-Relation :
    is-reflexive R → is-transitive R
  is-transitive-is-reflexive-is-right-contratransitive-Relation r =
    is-transitive-is-symmetric-is-right-contratransitive-Relation
      ( is-symmetric-is-reflexive-is-right-contratransitive-Relation R H r)
```

## See also

- [Strict symmetrization of binary relations](foundation.strict-symmetrization-binary-relations.md)
