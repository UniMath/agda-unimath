# Strict symmetrization of binary relations

```agda
module foundation.strict-symmetrization-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.outer-2-horn-filler-conditions-binary-relations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.identity-types
open import foundation-core.retractions
```

</details>

## Idea

Given a [binary relation](foundation.binary-relations.md) `R` on `A`, we can
construct a
{{#concept "strict symmetrization" Disambiguation="of binary relations valued in types" Agda=strict-symmetrization-Relation}}
of `R`. This is a relation `Rˢ` on `A` that is strictly
[symmetric](foundation.symmetric-binary-relations.md). I.e., for every
`r : Rˢ x y`, we have a symmetry operation `sym r : Rˢ y x` such that

```text
  sym (sym r) ≐ r.
```

If the underlying binary relation is
[reflexive](foundation.reflexive-relations.md), then this construction has a
unit map `R → Rˢ`. If the binary relation satisfies an
[outer horn filler condition](foundation.outer-2-horn-filler-conditions-binary-relations.md),
then it has a counit map `Rˢ → R`.

An essential fact about the strict symmetrization of a relation is that the
strict symmetrization of an identity relation is equivalent to the identity
relation. We consider the strict symmetrization if the standard identity
relation in
[`foundation.strictly-involutive-identity-types`](foundation.strictly-involutive-identity-types.md).

**Warning.** The strict symmetrization is not the symmetric closure in general.
For instance, if the underlying relation has an initial element, i.e., there is
an element `a` such that `R a x` is
[contractible](foundation-core.contractible-types.md) for every `x`, then the
strict symmetrization will be reflexive, while the symmetric closure need not
be.

## Definition

### Strict symmetrization of binary relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  strict-symmetrization-Relation : Relation (l1 ⊔ l2) A
  strict-symmetrization-Relation x y =
    Σ A (λ z → R z x × R z y)

  symmetric-strict-symmetrization-Relation :
    is-symmetric strict-symmetrization-Relation
  symmetric-strict-symmetrization-Relation x y (z , p , q) = (z , q , p)

  is-involution-symmetric-strict-symmetrization-Relation :
    {x y : A} (p : strict-symmetrization-Relation x y) →
    ( symmetric-strict-symmetrization-Relation y x
      ( symmetric-strict-symmetrization-Relation x y p)) ＝
    ( p)
  is-involution-symmetric-strict-symmetrization-Relation p = refl

  unit-strict-symmetrization-Relation :
    is-reflexive R →
    {x y : A} → R x y → strict-symmetrization-Relation x y
  unit-strict-symmetrization-Relation r {x} p = (x , r x , p)

  counit-strict-symmetrization-Relation :
    has-extensions-Relation R →
    {x y : A} → strict-symmetrization-Relation x y → R x y
  counit-strict-symmetrization-Relation H (_ , p , q) = H p q
```

### Dual strict symmetrization of binary relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  dual-strict-symmetrization-Relation : Relation (l1 ⊔ l2) A
  dual-strict-symmetrization-Relation x y =
    Σ A (λ z → R x z × R y z)

  symmetric-dual-strict-symmetrization-Relation :
    is-symmetric dual-strict-symmetrization-Relation
  symmetric-dual-strict-symmetrization-Relation x y (z , p , q) = (z , q , p)

  is-involution-symmetric-dual-strict-symmetrization-Relation :
    {x y : A} (p : dual-strict-symmetrization-Relation x y) →
    ( symmetric-dual-strict-symmetrization-Relation y x
      ( symmetric-dual-strict-symmetrization-Relation x y p)) ＝
    ( p)
  is-involution-symmetric-dual-strict-symmetrization-Relation p = refl

  unit-dual-strict-symmetrization-Relation :
    is-reflexive R →
    {x y : A} → R x y → dual-strict-symmetrization-Relation x y
  unit-dual-strict-symmetrization-Relation r {x} {y} p = (y , p , r y)

  counit-dual-strict-symmetrization-Relation :
    has-lifts-Relation R →
    {x y : A} → dual-strict-symmetrization-Relation x y → R x y
  counit-dual-strict-symmetrization-Relation H (_ , p , q) = H p q
```

## Properties

### The strict symmetrization of a reflexive relation is reflexive

In fact, `R` does not have to be reflexive for the strict symmetrization to be
reflexive. It suffices that there for every element of `A` is some other element
that relates to it. For instance, the strict symmetrization of a relation with
an initial element is always reflexive.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  refl-strict-symmetrization-Relation' :
    ((x : A) → Σ A (λ y → R y x)) →
    is-reflexive (strict-symmetrization-Relation R)
  refl-strict-symmetrization-Relation' r x =
    (pr1 (r x) , pr2 (r x) , pr2 (r x))

  refl-strict-symmetrization-Relation :
    is-reflexive R →
    is-reflexive (strict-symmetrization-Relation R)
  refl-strict-symmetrization-Relation r x = (x , r x , r x)
```

### The strict symmetrization of a relation with extensions satisfies all 2-horn filler conditions

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  (H : has-extensions-Relation R)
  where

  has-extensions-strict-symmetrization-Relation :
    has-extensions-Relation (strict-symmetrization-Relation R)
  has-extensions-strict-symmetrization-Relation
    {x} (_ , p , q) (_ , p' , q') = (x , H p q , H p' q')

  has-lifts-strict-symmetrization-has-extensions-Relation :
    has-lifts-Relation (strict-symmetrization-Relation R)
  has-lifts-strict-symmetrization-has-extensions-Relation
    {z = z} (w , p , q) (w' , p' , q') = (z , H q p , H q' p')

  transitive-strict-symmetrization-has-extensions-Relation :
    is-transitive (strict-symmetrization-Relation R)
  transitive-strict-symmetrization-has-extensions-Relation
    x y z (w , p , q) (w' , p' , q') = (y , H q' p' , H p q)
```

### If the extension operation on the underlying relation is left unital, then the counit is a retraction of the unit of the strict symmetrization

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  (r : is-reflexive R) (H : has-extensions-Relation R)
  where

  is-retraction-counit-strict-symmetrization-Relation :
    {x y : A} →
    ((p : R x y) → H (r x) p ＝ p) →
    is-retraction
      ( unit-strict-symmetrization-Relation R r {x} {y})
      ( counit-strict-symmetrization-Relation R H {x} {y})
  is-retraction-counit-strict-symmetrization-Relation s = s
```
