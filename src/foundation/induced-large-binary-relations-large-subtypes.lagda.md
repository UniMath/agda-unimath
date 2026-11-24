# Induced large binary relations on large subtypes

```agda
module foundation.induced-large-binary-relations-large-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.large-binary-relations
open import foundation.large-subtypes
open import foundation.universe-levels
```

</details>

## Idea

Given a [large subtype](foundation.large-subtypes.md) `S` of a
universe-polymorphic type `X : (l : Level) → UU (α l)`, any
[large binary relation](foundation.large-binary-relations.md) `R` on `X` induces
a large binary relation on `S`.

## Definition

```agda
module _
  {α γ : Level → Level} {β : Level → Level → Level}
  {X : (l : Level) → UU (α l)}
  (S : large-subtype γ X)
  where

  large-relation-large-subtype :
    Large-Relation β X → Large-Relation β (type-large-subtype S)
  large-relation-large-subtype R (x , _) (y , _) = R x y

  large-relation-prop-large-subtype :
    Large-Relation-Prop β X → Large-Relation-Prop β (type-large-subtype S)
  large-relation-prop-large-subtype R (x , _) (y , _) = R x y
```

## Properties

### The induced relation of a large subtype preserves reflexivity

```agda
module _
  {α γ : Level → Level} {β : Level → Level → Level}
  {X : (l : Level) → UU (α l)}
  (S : large-subtype γ X)
  (R : Large-Relation β X)
  where

  refl-large-relation-large-subtype :
    is-reflexive-Large-Relation X R →
    is-reflexive-Large-Relation
      ( type-large-subtype S)
      ( large-relation-large-subtype S R)
  refl-large-relation-large-subtype refl-R (x , _) = refl-R x
```

### The induced relation of a large subtype preserves symmetry

```agda
module _
  {α γ : Level → Level} {β : Level → Level → Level}
  {X : (l : Level) → UU (α l)}
  (S : large-subtype γ X)
  (R : Large-Relation β X)
  where

  is-symmetric-large-relation-large-subtype :
    is-symmetric-Large-Relation X R →
    is-symmetric-Large-Relation
      ( type-large-subtype S)
      ( large-relation-large-subtype S R)
  is-symmetric-large-relation-large-subtype sym-R (x , _) (y , _) = sym-R x y
```

### The induced relation of a large subtype preserves transitivity

```agda
module _
  {α γ : Level → Level} {β : Level → Level → Level}
  {X : (l : Level) → UU (α l)}
  (S : large-subtype γ X)
  (R : Large-Relation β X)
  where

  is-transitive-large-relation-large-subtype :
    is-transitive-Large-Relation X R →
    is-transitive-Large-Relation
      ( type-large-subtype S)
      ( large-relation-large-subtype S R)
  is-transitive-large-relation-large-subtype trans-R (x , _) (y , _) (z , _) =
    trans-R x y z
```
