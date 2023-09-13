# Disequality

```agda
module foundation.disequality where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.action-on-identifications-functions
open import foundation.apartness-relations
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.identity-types
open import foundation.negation
open import foundation-core.propositions
```

</details>

## Idea

Two terms `x` and `y` are **disequal** whenever `¬ (x ＝ y)` is inhabited.

## Definition

```agda
disequal : {l : Level} {A : UU l} → A → A → UU l
disequal x y = ¬ (x ＝ y)

infix 7 _≠_
_≠_ = disequal
```

## Properties

### Disequality is a property

```agda
module _
  {l : Level} {A : UU l}
  where

  is-prop-disequal : {x y : A} → is-prop (x ≠ y)
  is-prop-disequal = is-prop-neg

  disequal-Prop : (x y : A) → Prop l
  pr1 (disequal-Prop x y) = x ≠ y
  pr2 (disequal-Prop x y) = is-prop-disequal
```

### Disequality is antireflexive

```agda
module _
  {l : Level} {A : UU l}
  where

  is-antireflexive-disequal : is-antireflexive (disequal-Prop {A = A})
  is-antireflexive-disequal a d = d refl

  is-consistent-disequal : is-consistent (disequal-Prop {A = A})
  is-consistent-disequal a b p d = d p
```

### Disequality is symmetric

```agda
module _
  {l : Level} {A : UU l}
  where

  is-symmetric-disequal : is-symmetric (disequal {A = A})
  is-symmetric-disequal a b = map-neg inv
```

### If two functions are disequal at a point, they are disequal as functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  disequal-Π : (f g : (x : A) → B x) (a : A) → f a ≠ g a → f ≠ g
  disequal-Π f g a = map-neg (λ h → htpy-eq h a)
```

### If either component of two pairs are disequal, the pairs are disequal

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  disequal-pr1 : (u v : Σ A B) → pr1 u ≠ pr1 v → u ≠ v
  disequal-pr1 u v = map-neg (ap pr1)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  disequal-prod-pr2 : (u v : A × B) → pr2 u ≠ pr2 v → u ≠ v
  disequal-prod-pr2 u v = map-neg (ap pr2)
```

### If there is a reflexive relation that does not relate `a` and `b`, then they are disequal

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  disequal-reflexive-relation :
    (R : Relation l2 A) → is-reflexive R → (a b : A) → ¬ (R a b) → a ≠ b
  disequal-reflexive-relation R is-refl-R a .a r refl = r (is-refl-R a)
```

### If there is any family on `A` that is inhabited over one term but not the other, then they are disequal

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  disequal-leibniz : (B : A → UU l2) → (a b : A) → B a → ¬ (B b) → a ≠ b
  disequal-leibniz B a .a a' b' refl = b' a'

  disequal-leibniz' : (B : A → UU l2) → (a b : A) → ¬ (B a) → B b → a ≠ b
  disequal-leibniz' B a .a a' b' refl = a' b'
```

## See also

- [Apartness relations](foundation.apartness-relations.md)
