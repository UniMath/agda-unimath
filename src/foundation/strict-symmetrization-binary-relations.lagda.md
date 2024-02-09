# Strict symmetrization of binary relations

```agda
module foundation.strict-symmetrization-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.iterated-dependent-product-types
open import foundation.subtypes
open import foundation.contratransitive-binary-relations
open import foundation.function-types
open import foundation.homotopies
open import foundation.binary-relations
open import foundation.transitive-binary-relations
open import foundation.reflexive-relations
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.retractions
open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

Given a [binary relation](foundation.binary-relations.md) `R` on `A`, we can
construct the {{#concept "strict symmetrization"}} of `R`. This is another
relation `Rˢ` on `A` that is strictly
[symmetric](foundation.binary-relations.md). I.e., for every `r : R' x y`, we
have a symmetry operation `sym r : R' y x` such that

```text
  sym (sym r) ≐ r.
```

If the underlying binary relation is
[reflexive](foundation.reflexive-relations.md), then this construction has a map
`R → Rˢ`. if the binary relation is (right)
[contratransitive](foundation.contratransitive-binary-relations.md), then it has
a map `Rˢ → R`.

## Definition

### The strict symmetrization construction on binary relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  strict-symmetrization-Relation : Relation (l1 ⊔ l2) A
  strict-symmetrization-Relation x y =
    Σ A (λ z → R z x × R z y)

  is-symmetric-strict-symmetrization-Relation :
    is-symmetric strict-symmetrization-Relation
  is-symmetric-strict-symmetrization-Relation x y (z , p , q) = (z , q , p)

  is-involution-is-symmetric-strict-symmetrization-Relation :
    {x y : A} (p : strict-symmetrization-Relation x y) →
    ( is-symmetric-strict-symmetrization-Relation y x
      ( is-symmetric-strict-symmetrization-Relation x y p)) ＝
    ( p)
  is-involution-is-symmetric-strict-symmetrization-Relation p = refl

  unit-strict-symmetrization-Relation :
    is-reflexive R →
    {x y : A} → R x y → strict-symmetrization-Relation x y
  unit-strict-symmetrization-Relation r {x} p = (x , r x , p)

  counit-strict-symmetrization-Relation :
    is-right-contratransitive R →
    {x y : A} → strict-symmetrization-Relation x y → R x y
  counit-strict-symmetrization-Relation H (_ , p , q) = H p q
```

### The strict symmetrization of a reflexive relation is reflexive

In fact, `R` does not have to be reflexive for the strict symmetrization to be
reflexive. It suffices that there, for every element of `A` is some other
element that relates to it. For instance, every relation with an initial element
will have strict symmetrization that is reflexive.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-reflexive-strict-symmetrization-Relation' :
    ((x : A) → Σ A (λ y → R y x)) →
    is-reflexive (strict-symmetrization-Relation R)
  is-reflexive-strict-symmetrization-Relation' r x =
    (pr1 (r x) , pr2 (r x) , pr2 (r x))

  is-reflexive-strict-symmetrization-Relation :
    is-reflexive R →
    is-reflexive (strict-symmetrization-Relation R)
  is-reflexive-strict-symmetrization-Relation r x = (x , r x , r x)
```

### The strict symmetrization of a contratransitive relation satisfies all 2-horn filler conditions

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  (H : is-right-contratransitive R)
  where

  is-right-contratransitive-strict-symmetrization-Relation :
    is-right-contratransitive (strict-symmetrization-Relation R)
  is-right-contratransitive-strict-symmetrization-Relation
    {x} (_ , p , q) (_ , p' , q') = (x , H p q , H p' q')

  is-left-contratransitive-strict-symmetrization-Relation :
    is-left-contratransitive (strict-symmetrization-Relation R)
  is-left-contratransitive-strict-symmetrization-Relation
    {z = z} (w , p , q) (w' , p' , q') = (z , H q p , H q' p')

  is-transitive-strict-symmetrization-Relation :
    is-transitive (strict-symmetrization-Relation R)
  is-transitive-strict-symmetrization-Relation
    x y z (w , p , q) (w' , p' , q') = (y , H q' p' , H p q)
```

### If the contratransitivity operation is left unital, then the counit is a retraction of the unit of the strict symmetrization

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  (r : is-reflexive R) (H : is-right-contratransitive R)
  where

  is-retraction-counit-strict-symmetrization-Relation :
    {x y : A} →
    ((p : R x y) → H (r x) p ＝ p) →
    is-retraction
      ( unit-strict-symmetrization-Relation R r {x} {y})
      ( counit-strict-symmetrization-Relation R H {x} {y})
  is-retraction-counit-strict-symmetrization-Relation s = s
```

## See also

- [Strictly involutive identity types](foundation.strictly-involutive-identity-types.md)
