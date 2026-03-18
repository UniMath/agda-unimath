# The algebraic theory of semigroups

```agda
module universal-algebra.algebraic-theory-of-semigroups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.binary-homotopies
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups
open import group-theory.semigroups

open import lists.tuples

open import univalent-combinatorics.classical-finite-types

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras
open import universal-algebra.homomorphisms-of-algebras
open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
```

</details>

## Idea

There is an
{{#concept "algebraic theory of semigroups" Agda=algebraic-theory-Semigroup}}.
The type of all such [algebras](universal-algebra.algebras.md) is
[equivalent](foundation-core.equivalences.md) to the type of
[semigroups](group-theory.semigroups.md).

## Definition

```agda
data semigroup-ops : UU lzero where
  mul-semigroup-op : semigroup-ops

semigroup-signature : signature lzero
pr1 semigroup-signature = semigroup-ops
pr2 semigroup-signature mul-semigroup-op = 2

data semigroup-laws : UU lzero where
  associative-semigroup-law : semigroup-laws

algebraic-theory-Semigroup : Algebraic-Theory lzero semigroup-signature
pr1 algebraic-theory-Semigroup = semigroup-laws
pr2 algebraic-theory-Semigroup associative-semigroup-law =
  let
    var : (i : ℕ) → {le-ℕ i 3} → term semigroup-signature 3
    var i {i<3} = var-term (standard-classical-Fin 3 (i , i<3))
    _*_ x y = op-term mul-semigroup-op (x ∷ y ∷ empty-tuple)
  in
    ( 3 ,
      (var 0 * var 1) * var 2 ,
      var 0 * (var 1 * var 2))

Algebra-Semigroup : (l : Level) → UU (lsuc l)
Algebra-Semigroup l =
  Algebra l semigroup-signature algebraic-theory-Semigroup
```

## Properties

### The algebra of semigroups is equivalent to the type of semigroups

```agda
module _
  {l : Level}
  (((set-A , models-A) , satisfies-A) : Algebra-Semigroup l)
  where

  type-Algebra-Semigroup : UU l
  type-Algebra-Semigroup = type-Set set-A

  mul-Algebra-Semigroup :
    type-Algebra-Semigroup → type-Algebra-Semigroup → type-Algebra-Semigroup
  mul-Algebra-Semigroup x y =
    models-A mul-semigroup-op (x ∷ y ∷ empty-tuple)

  associative-mul-Algebra-Semigroup :
    (x y z : type-Algebra-Semigroup) →
    mul-Algebra-Semigroup (mul-Algebra-Semigroup x y) z ＝
    mul-Algebra-Semigroup x (mul-Algebra-Semigroup y z)
  associative-mul-Algebra-Semigroup x y z =
    satisfies-A
      ( associative-semigroup-law)
      ( component-tuple 3 (z ∷ y ∷ x ∷ empty-tuple))

  semigroup-Algebra-Semigroup : Semigroup l
  semigroup-Algebra-Semigroup =
    ( set-A ,
      mul-Algebra-Semigroup ,
      associative-mul-Algebra-Semigroup)

module _
  {l : Level}
  (G : Semigroup l)
  where

  is-model-of-semigroup-signature-Semigroup :
    is-model-of-signature semigroup-signature (set-Semigroup G)
  is-model-of-semigroup-signature-Semigroup
    mul-semigroup-op (x ∷ y ∷ empty-tuple) =
    mul-Semigroup G x y

  model-of-semigroup-signature-Semigroup :
    Model-Of-Signature l semigroup-signature
  model-of-semigroup-signature-Semigroup =
    ( set-Semigroup G ,
      is-model-of-semigroup-signature-Semigroup)

  is-algebra-semigroup-Semigroup :
    is-algebra-Model-of-Signature
      ( semigroup-signature)
      ( algebraic-theory-Semigroup)
      ( model-of-semigroup-signature-Semigroup)
  is-algebra-semigroup-Semigroup associative-semigroup-law xs =
    associative-mul-Semigroup G _ _ _

  algebra-semigroup-Semigroup : Algebra-Semigroup l
  algebra-semigroup-Semigroup =
    ( model-of-semigroup-signature-Semigroup ,
      is-algebra-semigroup-Semigroup)

abstract
  is-section-semigroup-Algebra-Semigroup :
    {l : Level} (A : Algebra-Semigroup l) →
    algebra-semigroup-Semigroup (semigroup-Algebra-Semigroup A) ＝ A
  is-section-semigroup-Algebra-Semigroup A =
    eq-type-subtype
      ( is-algebra-prop-Model-Of-Signature
        ( semigroup-signature)
        ( algebraic-theory-Semigroup))
      ( eq-pair-eq-fiber
        ( eq-binary-htpy _ _
          λ where
            mul-semigroup-op (x ∷ y ∷ empty-tuple) → refl))

  is-retraction-semigroup-Algebra-Semigroup :
    {l : Level} (G : Semigroup l) →
    semigroup-Algebra-Semigroup (algebra-semigroup-Semigroup G) ＝ G
  is-retraction-semigroup-Algebra-Semigroup G = refl

is-equiv-semigroup-Algebra-Semigroup :
  {l : Level} → is-equiv (algebra-semigroup-Semigroup {l})
is-equiv-semigroup-Algebra-Semigroup =
  is-equiv-is-invertible
    ( semigroup-Algebra-Semigroup)
    ( is-section-semigroup-Algebra-Semigroup)
    ( is-retraction-semigroup-Algebra-Semigroup)

equiv-semigroup-Algebra-Semigroup :
  {l : Level} → Semigroup l ≃ Algebra-Semigroup l
equiv-semigroup-Algebra-Semigroup =
  ( algebra-semigroup-Semigroup ,
    is-equiv-semigroup-Algebra-Semigroup)
```

### Homomorphisms of semigroups are equivalent to homomorphisms of the algebras of semigroups

```agda
hom-algebra-semigroup-hom-Semigroup :
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2) →
  hom-Semigroup G H →
  hom-Algebra
    ( semigroup-signature)
    ( algebraic-theory-Semigroup)
    ( algebra-semigroup-Semigroup G)
    ( algebra-semigroup-Semigroup H)
hom-algebra-semigroup-hom-Semigroup _ _ (map-f , preserves-mul-f) =
  ( map-f ,
    λ where
      mul-semigroup-op (x ∷ y ∷ empty-tuple) → preserves-mul-f)

hom-semigroup-hom-Algebra-Semigroup :
  {l1 l2 : Level} (G : Algebra-Semigroup l1) (H : Algebra-Semigroup l2) →
  hom-Algebra semigroup-signature algebraic-theory-Semigroup G H →
  hom-Semigroup
    ( semigroup-Algebra-Semigroup G)
    ( semigroup-Algebra-Semigroup H)
hom-semigroup-hom-Algebra-Semigroup G H (map-f , preserves-ops-f) =
  ( map-f ,
    preserves-ops-f mul-semigroup-op (_ ∷ _ ∷ empty-tuple))
```
