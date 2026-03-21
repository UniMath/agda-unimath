# The algebraic theory of semigroups

```agda
module universal-algebra.algebraic-theory-of-semigroups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.binary-homotopies
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups
open import group-theory.semigroups

open import lists.tuples

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
data operation-Semigroup : UU lzero where
  mul-operation-Semigroup : operation-Semigroup

signature-Semigroup : signature lzero
pr1 signature-Semigroup = operation-Semigroup
pr2 signature-Semigroup mul-operation-Semigroup = 2

data law-Semigroup : UU lzero where
  associative-mul-law-Semigroup : law-Semigroup

algebraic-theory-Semigroup : Algebraic-Theory lzero signature-Semigroup
pr1 algebraic-theory-Semigroup = law-Semigroup
pr2 algebraic-theory-Semigroup associative-mul-law-Semigroup =
  let
    var : (i : ℕ) → term signature-Semigroup 3
    var i = var-term (mod-succ-ℕ 2 i)
    _*_ x y = op-term mul-operation-Semigroup (x ∷ y ∷ empty-tuple)
  in
    ( 3 ,
      (var 0 * var 1) * var 2 ,
      var 0 * (var 1 * var 2))

Algebra-Semigroup : (l : Level) → UU (lsuc l)
Algebra-Semigroup l =
  Algebra l signature-Semigroup algebraic-theory-Semigroup
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
    models-A mul-operation-Semigroup (x ∷ y ∷ empty-tuple)

  associative-mul-Algebra-Semigroup :
    (x y z : type-Algebra-Semigroup) →
    mul-Algebra-Semigroup (mul-Algebra-Semigroup x y) z ＝
    mul-Algebra-Semigroup x (mul-Algebra-Semigroup y z)
  associative-mul-Algebra-Semigroup x y z =
    satisfies-A
      ( associative-mul-law-Semigroup)
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

  is-model-Semigroup :
    is-model-of-signature signature-Semigroup (set-Semigroup G)
  is-model-Semigroup
    mul-operation-Semigroup (x ∷ y ∷ empty-tuple) =
    mul-Semigroup G x y

  model-Semigroup :
    Model-Of-Signature l signature-Semigroup
  model-Semigroup = (set-Semigroup G , is-model-Semigroup)

  is-algebra-model-Semigroup :
    is-algebra-Model-of-Signature
      ( signature-Semigroup)
      ( algebraic-theory-Semigroup)
      ( model-Semigroup)
  is-algebra-model-Semigroup associative-mul-law-Semigroup xs =
    associative-mul-Semigroup G _ _ _

  algebra-semigroup-Semigroup : Algebra-Semigroup l
  algebra-semigroup-Semigroup =
    ( model-Semigroup ,
      is-algebra-model-Semigroup)

abstract
  is-section-semigroup-Algebra-Semigroup :
    {l : Level} (A : Algebra-Semigroup l) →
    algebra-semigroup-Semigroup (semigroup-Algebra-Semigroup A) ＝ A
  is-section-semigroup-Algebra-Semigroup A =
    eq-type-subtype
      ( is-algebra-prop-Model-Of-Signature
        ( signature-Semigroup)
        ( algebraic-theory-Semigroup))
      ( eq-pair-eq-fiber
        ( eq-binary-htpy _ _
          λ where
            mul-operation-Semigroup (x ∷ y ∷ empty-tuple) → refl))

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
hom-Algebra-Semigroup :
  {l1 l2 : Level} → Algebra-Semigroup l1 → Algebra-Semigroup l2 → UU (l1 ⊔ l2)
hom-Algebra-Semigroup =
  hom-Algebra signature-Semigroup algebraic-theory-Semigroup

hom-semigroup-hom-Algebra-Semigroup :
  {l1 l2 : Level} (G : Algebra-Semigroup l1) (H : Algebra-Semigroup l2) →
  hom-Algebra-Semigroup G H →
  hom-Semigroup
    ( semigroup-Algebra-Semigroup G)
    ( semigroup-Algebra-Semigroup H)
hom-semigroup-hom-Algebra-Semigroup G H (map-f , preserves-ops-f) =
  ( map-f ,
    preserves-ops-f mul-operation-Semigroup (_ ∷ _ ∷ empty-tuple))

module _
  {l1 l2 : Level}
  (G : Semigroup l1)
  (H : Semigroup l2)
  where

  hom-algebra-semigroup-hom-Semigroup :
    hom-Semigroup G H →
    hom-Algebra-Semigroup
      ( algebra-semigroup-Semigroup G)
      ( algebra-semigroup-Semigroup H)
  hom-algebra-semigroup-hom-Semigroup (map-f , preserves-mul-f) =
    ( map-f ,
      λ where
        mul-operation-Semigroup (x ∷ y ∷ empty-tuple) → preserves-mul-f)

  is-equiv-hom-algebra-semigroup-hom-Semigroup :
    is-equiv hom-algebra-semigroup-hom-Semigroup
  is-equiv-hom-algebra-semigroup-hom-Semigroup =
    is-equiv-is-invertible
      ( hom-semigroup-hom-Algebra-Semigroup
        ( algebra-semigroup-Semigroup G)
        ( algebra-semigroup-Semigroup H))
      ( λ φ →
        eq-htpy-hom-Algebra
          ( signature-Semigroup)
          ( algebraic-theory-Semigroup)
          ( algebra-semigroup-Semigroup G)
          ( algebra-semigroup-Semigroup H)
          ( _)
          ( φ)
          ( refl-htpy))
      ( λ φ → eq-htpy-hom-Semigroup G H refl-htpy)

  equiv-hom-semigroup-hom-Algebra-Semigroup :
    hom-Semigroup G H ≃
    hom-Algebra-Semigroup
      ( algebra-semigroup-Semigroup G)
      ( algebra-semigroup-Semigroup H)
  equiv-hom-semigroup-hom-Algebra-Semigroup =
    ( hom-algebra-semigroup-hom-Semigroup ,
      is-equiv-hom-algebra-semigroup-hom-Semigroup)
```
