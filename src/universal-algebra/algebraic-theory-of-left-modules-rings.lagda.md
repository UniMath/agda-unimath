# The algebraic theory of left modules over rings

```agda
{-# OPTIONS --lossy-unification #-}

module universal-algebra.algebraic-theory-of-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.endomorphism-rings-abelian-groups
open import group-theory.homomorphisms-abelian-groups

open import linear-algebra.left-modules-rings
open import linear-algebra.linear-maps-left-modules-rings

open import lists.tuples

open import ring-theory.homomorphisms-rings
open import ring-theory.rings

open import univalent-combinatorics.standard-finite-types

open import universal-algebra.abstract-equations-over-signatures
open import universal-algebra.algebraic-theories
open import universal-algebra.algebraic-theory-of-abelian-groups
open import universal-algebra.algebras
open import universal-algebra.extensions-signatures
open import universal-algebra.homomorphisms-of-algebras
open import universal-algebra.isomorphisms-of-algebras
open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
```

</details>

## Idea

There is an
{{#concept "algebraic theory of left modules" Agda=algebraic-theory-left-module-Ring}}
over any [ring](ring-theory.rings.md).

The type of all such [algebras](universal-algebra.algebras.md) is
[equivalent](foundation-core.equivalences.md) to the type of
[left modules over the ring](linear-algebra.left-modules-rings.md).

## Definition

```agda
module _
  {l : Level}
  (R : Ring l)
  where

  data operation-left-module-Ring : UU l where
    operation-left-module-ring-operation-Ab :
      operation-Ab → operation-left-module-Ring
    mul-operation-left-module-Ring :
      type-Ring R → operation-left-module-Ring

  pattern zero-operation-left-module-Ring =
    operation-left-module-ring-operation-Ab zero-operation-Ab
  pattern add-operation-left-module-Ring =
    operation-left-module-ring-operation-Ab add-operation-Ab
  pattern neg-operation-left-module-Ring =
    operation-left-module-ring-operation-Ab neg-operation-Ab

  signature-left-module-Ring : signature l
  pr1 signature-left-module-Ring = operation-left-module-Ring
  pr2 signature-left-module-Ring
    ( operation-left-module-ring-operation-Ab op) =
    arity-operation-signature signature-Ab op
  pr2 signature-left-module-Ring (mul-operation-left-module-Ring _) = 1

  data law-left-module-Ring : UU l where
    law-left-module-ring-law-Ab : law-Ab → law-left-module-Ring
    left-distributive-mul-add-law-left-module-Ring :
      type-Ring R → law-left-module-Ring
    right-distributive-mul-add-law-left-module-Ring :
      type-Ring R → type-Ring R → law-left-module-Ring
    left-unit-mul-law-left-module-Ring : law-left-module-Ring
    associative-mul-law-left-module-Ring :
      type-Ring R → type-Ring R → law-left-module-Ring

  pattern associative-add-law-left-module-Ring =
    law-left-module-ring-law-Ab associative-add-law-Ab
  pattern left-unit-add-law-left-module-Ring =
    law-left-module-ring-law-Ab left-unit-add-law-Ab
  pattern right-unit-add-law-left-module-Ring =
    law-left-module-ring-law-Ab right-unit-add-law-Ab
  pattern left-inverse-add-law-left-module-Ring =
    law-left-module-ring-law-Ab left-inverse-add-law-Ab
  pattern right-inverse-add-law-left-module-Ring =
    law-left-module-ring-law-Ab right-inverse-add-law-Ab
  pattern commutative-add-law-left-module-Ring =
    law-left-module-ring-law-Ab commutative-add-law-Ab

  extension-signature-ab-left-module-Ring :
    is-extension-of-signature signature-Ab signature-left-module-Ring
  pr1 extension-signature-ab-left-module-Ring =
    operation-left-module-ring-operation-Ab
  pr2 extension-signature-ab-left-module-Ring _ = refl

  algebraic-theory-left-module-Ring :
    Algebraic-Theory l signature-left-module-Ring
  pr1 algebraic-theory-left-module-Ring = law-left-module-Ring
  pr2 algebraic-theory-left-module-Ring =
    let
      var : (i k : ℕ) → term signature-left-module-Ring (succ-ℕ k)
      var i k = var-term (mod-succ-ℕ k i)
      add-term :
        {k : ℕ} →
        term signature-left-module-Ring k →
        term signature-left-module-Ring k →
        term signature-left-module-Ring k
      add-term x y =
        op-term add-operation-left-module-Ring (x ∷ y ∷ empty-tuple)
      mul-term :
        {k : ℕ} →
        type-Ring R → term signature-left-module-Ring k →
        term signature-left-module-Ring k
      mul-term r x =
        op-term (mul-operation-left-module-Ring r) (x ∷ empty-tuple)
    in
      λ where
        ( law-left-module-ring-law-Ab law) →
          translation-abstract-equation
            ( signature-Ab)
            ( signature-left-module-Ring)
            ( extension-signature-ab-left-module-Ring)
            ( index-abstract-equation-Algebraic-Theory
              ( signature-Ab)
              ( algebraic-theory-Ab)
              ( law))
        ( left-distributive-mul-add-law-left-module-Ring r) →
          ( 2 ,
            mul-term r (add-term (var 0 1) (var 1 1)) ,
            add-term (mul-term r (var 0 1)) (mul-term r (var 1 1)))
        ( right-distributive-mul-add-law-left-module-Ring r s) →
          ( 1 ,
            mul-term (add-Ring R r s) (var 0 0) ,
            add-term (mul-term r (var 0 0)) (mul-term s (var 0 0)))
        left-unit-mul-law-left-module-Ring →
          ( 1 ,
            mul-term (one-Ring R) (var 0 0) ,
            var 0 0)
        ( associative-mul-law-left-module-Ring r s) →
          ( 1 ,
            mul-term (mul-Ring R r s) (var 0 0) ,
            mul-term r (mul-term s (var 0 0)))

Algebra-Left-Module-Ring :
  {l1 : Level} (l2 : Level) → Ring l1 → UU (l1 ⊔ lsuc l2)
Algebra-Left-Module-Ring l2 R =
  Algebra
    ( l2)
    ( signature-left-module-Ring R)
    ( algebraic-theory-left-module-Ring R)
```

## Properties

### Left modules from algebras in the theory of left modules of rings

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (A@((set-A , model-A) , satisfies-A) : Algebra-Left-Module-Ring l2 R)
  where

  algebra-ab-Algebra-Left-Module-Ring : Algebra-Ab l2
  algebra-ab-Algebra-Left-Module-Ring =
    ( ( set-A , model-A ∘ operation-left-module-ring-operation-Ab) ,
      λ where
        left-inverse-add-law-Ab →
          satisfies-A left-inverse-add-law-left-module-Ring
        right-inverse-add-law-Ab →
          satisfies-A right-inverse-add-law-left-module-Ring
        left-unit-add-law-Ab →
          satisfies-A left-unit-add-law-left-module-Ring
        right-unit-add-law-Ab →
          satisfies-A right-unit-add-law-left-module-Ring
        associative-add-law-Ab →
          satisfies-A associative-add-law-left-module-Ring
        commutative-add-law-Ab →
          satisfies-A commutative-add-law-left-module-Ring)

  ab-Algebra-Left-Module-Ring : Ab l2
  ab-Algebra-Left-Module-Ring =
    ab-Algebra-Ab algebra-ab-Algebra-Left-Module-Ring

  type-Algebra-Left-Module-Ring : UU l2
  type-Algebra-Left-Module-Ring = type-Set set-A

  add-Algebra-Left-Module-Ring :
    type-Algebra-Left-Module-Ring → type-Algebra-Left-Module-Ring →
    type-Algebra-Left-Module-Ring
  add-Algebra-Left-Module-Ring = add-Ab ab-Algebra-Left-Module-Ring

  mul-Algebra-Left-Module-Ring :
    type-Ring R → type-Algebra-Left-Module-Ring → type-Algebra-Left-Module-Ring
  mul-Algebra-Left-Module-Ring r x =
    model-A (mul-operation-left-module-Ring r) (x ∷ empty-tuple)

  left-distributive-law-mul-add-Algebra-Left-Module-Ring :
    (r : type-Ring R) (x y : type-Algebra-Left-Module-Ring) →
    mul-Algebra-Left-Module-Ring r
      ( add-Algebra-Left-Module-Ring x y) ＝
    add-Algebra-Left-Module-Ring
      ( mul-Algebra-Left-Module-Ring r x)
      ( mul-Algebra-Left-Module-Ring r y)
  left-distributive-law-mul-add-Algebra-Left-Module-Ring r x y =
    satisfies-A
      ( left-distributive-mul-add-law-left-module-Ring r)
      ( component-tuple 2 (y ∷ x ∷ empty-tuple))

  right-distributive-law-mul-add-Algebra-Left-Module-Ring :
    (r s : type-Ring R) (x : type-Algebra-Left-Module-Ring) →
    mul-Algebra-Left-Module-Ring (add-Ring R r s) x ＝
    add-Algebra-Left-Module-Ring
      ( mul-Algebra-Left-Module-Ring r x)
      ( mul-Algebra-Left-Module-Ring s x)
  right-distributive-law-mul-add-Algebra-Left-Module-Ring r s x =
    satisfies-A
      ( right-distributive-mul-add-law-left-module-Ring r s)
      ( λ _ → x)

  associative-mul-Algebra-Left-Module-Ring :
    (r s : type-Ring R) (x : type-Algebra-Left-Module-Ring) →
    mul-Algebra-Left-Module-Ring (mul-Ring R r s) x ＝
    mul-Algebra-Left-Module-Ring r (mul-Algebra-Left-Module-Ring s x)
  associative-mul-Algebra-Left-Module-Ring r s x =
    satisfies-A
      ( associative-mul-law-left-module-Ring r s)
      ( λ _ → x)

  left-unit-law-mul-Algebra-Left-Module-Ring :
    (x : type-Algebra-Left-Module-Ring) →
    mul-Algebra-Left-Module-Ring (one-Ring R) x ＝ x
  left-unit-law-mul-Algebra-Left-Module-Ring x =
    satisfies-A left-unit-mul-law-left-module-Ring (λ _ → x)

  left-module-Algebra-Left-Module-Ring : left-module-Ring l2 R
  left-module-Algebra-Left-Module-Ring =
    make-left-module-Ring
      ( R)
      ( ab-Algebra-Left-Module-Ring)
      ( mul-Algebra-Left-Module-Ring)
      ( left-distributive-law-mul-add-Algebra-Left-Module-Ring)
      ( right-distributive-law-mul-add-Algebra-Left-Module-Ring)
      ( left-unit-law-mul-Algebra-Left-Module-Ring)
      ( associative-mul-Algebra-Left-Module-Ring)
```

### Algebras in the theory of left modules over rings from left modules over rings

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  algebra-ab-left-module-Ring : Algebra-Ab l2
  algebra-ab-left-module-Ring = algebra-ab-Ab (ab-left-module-Ring R M)

  is-model-set-left-module-Ring :
    is-model-of-signature
      ( signature-left-module-Ring R)
      ( set-left-module-Ring R M)
  is-model-set-left-module-Ring (operation-left-module-ring-operation-Ab op) =
    is-model-set-Algebra
      ( signature-Ab)
      ( algebraic-theory-Ab)
      ( algebra-ab-left-module-Ring)
      ( op)
  is-model-set-left-module-Ring
    (mul-operation-left-module-Ring r) (x ∷ empty-tuple) =
    mul-left-module-Ring R M r x

  model-left-module-Ring :
    Model-Of-Signature l2 (signature-left-module-Ring R)
  model-left-module-Ring =
    ( set-left-module-Ring R M ,
      is-model-set-left-module-Ring)

  is-algebra-model-left-module-Ring :
    is-algebra-Model-of-Signature
      ( signature-left-module-Ring R)
      ( algebraic-theory-left-module-Ring R)
      ( model-left-module-Ring)
  is-algebra-model-left-module-Ring associative-add-law-left-module-Ring xs =
    associative-add-left-module-Ring R M _ _ _
  is-algebra-model-left-module-Ring left-unit-add-law-left-module-Ring xs =
    left-unit-law-add-left-module-Ring R M _
  is-algebra-model-left-module-Ring right-unit-add-law-left-module-Ring xs =
    right-unit-law-add-left-module-Ring R M _
  is-algebra-model-left-module-Ring left-inverse-add-law-left-module-Ring xs =
    left-inverse-law-add-left-module-Ring R M _
  is-algebra-model-left-module-Ring right-inverse-add-law-left-module-Ring xs =
    right-inverse-law-add-left-module-Ring R M _
  is-algebra-model-left-module-Ring
    (left-distributive-mul-add-law-left-module-Ring r) xs =
    left-distributive-mul-add-left-module-Ring R M r _ _
  is-algebra-model-left-module-Ring
    (right-distributive-mul-add-law-left-module-Ring r s) xs =
    right-distributive-mul-add-left-module-Ring R M r s _
  is-algebra-model-left-module-Ring commutative-add-law-left-module-Ring xs =
    commutative-add-left-module-Ring R M _ _
  is-algebra-model-left-module-Ring left-unit-mul-law-left-module-Ring xs =
    left-unit-law-mul-left-module-Ring R M _
  is-algebra-model-left-module-Ring
    (associative-mul-law-left-module-Ring r s) xs =
    associative-mul-left-module-Ring R M r s _

  algebra-left-module-left-module-Ring :
    Algebra-Left-Module-Ring l2 R
  algebra-left-module-left-module-Ring =
    ( model-left-module-Ring , is-algebra-model-left-module-Ring)
```

### The type of left modules over rings is equivalent to the type of algebras in the theory of left modules

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  where

  preserves-operations-id-is-section-left-module-Algebra-Left-Module-Ring :
    (A : Algebra-Left-Module-Ring l2 R) →
    preserves-operations-Algebra
      ( signature-left-module-Ring R)
      ( algebraic-theory-left-module-Ring R)
      ( algebra-left-module-left-module-Ring R
        ( left-module-Algebra-Left-Module-Ring R A))
      ( A)
      ( id)
  preserves-operations-id-is-section-left-module-Algebra-Left-Module-Ring A =
    λ where
      add-operation-left-module-Ring (x ∷ y ∷ empty-tuple) → refl
      neg-operation-left-module-Ring (x ∷ empty-tuple) → refl
      zero-operation-left-module-Ring empty-tuple → refl
      (mul-operation-left-module-Ring r) (x ∷ empty-tuple) → refl

  hom-is-section-left-module-Algebra-Left-Module-Ring :
    (A : Algebra-Left-Module-Ring l2 R) →
    hom-Algebra
      ( signature-left-module-Ring R)
      ( algebraic-theory-left-module-Ring R)
      ( algebra-left-module-left-module-Ring R
        ( left-module-Algebra-Left-Module-Ring R A))
      ( A)
  hom-is-section-left-module-Algebra-Left-Module-Ring A =
    ( id ,
      preserves-operations-id-is-section-left-module-Algebra-Left-Module-Ring A)

  iso-is-section-left-module-Algebra-Left-Module-Ring :
    (A : Algebra-Left-Module-Ring l2 R) →
    iso-Algebra
      ( signature-left-module-Ring R)
      ( algebraic-theory-left-module-Ring R)
      ( algebra-left-module-left-module-Ring R
        ( left-module-Algebra-Left-Module-Ring R A))
      ( A)
  iso-is-section-left-module-Algebra-Left-Module-Ring A =
    ( hom-is-section-left-module-Algebra-Left-Module-Ring A ,
      is-iso-is-equiv-hom-Algebra
        ( signature-left-module-Ring R)
        ( algebraic-theory-left-module-Ring R)
        ( algebra-left-module-left-module-Ring R
          ( left-module-Algebra-Left-Module-Ring R A))
        ( A)
        ( hom-is-section-left-module-Algebra-Left-Module-Ring A)
        ( is-equiv-id))

  abstract
    is-section-left-module-Algebra-Left-Module-Ring :
      (A : Algebra-Left-Module-Ring l2 R) →
      algebra-left-module-left-module-Ring R
        ( left-module-Algebra-Left-Module-Ring R A) ＝
      A
    is-section-left-module-Algebra-Left-Module-Ring A =
      eq-iso-Algebra _ _ _ _
        ( iso-is-section-left-module-Algebra-Left-Module-Ring A)

    is-retraction-left-module-Algebra-Left-Module-Ring :
      (M : left-module-Ring l2 R) →
      left-module-Algebra-Left-Module-Ring R
        ( algebra-left-module-left-module-Ring R M) ＝
      M
    is-retraction-left-module-Algebra-Left-Module-Ring M =
      let
        A = ab-left-module-Ring R M
      in
        eq-pair-eq-fiber
          ( eq-htpy-hom-Ring
            ( R)
            ( endomorphism-ring-Ab A)
            ( _)
            ( _)
            ( λ r → eq-htpy-hom-Ab A A refl-htpy))

  is-equiv-algebra-left-module-left-module-Ring :
    is-equiv
      ( algebra-left-module-left-module-Ring {l2 = l2} R)
  is-equiv-algebra-left-module-left-module-Ring =
    is-equiv-is-invertible
      ( left-module-Algebra-Left-Module-Ring R)
      ( is-section-left-module-Algebra-Left-Module-Ring)
      ( is-retraction-left-module-Algebra-Left-Module-Ring)

  equiv-left-module-Algebra-Left-Module-Ring :
    left-module-Ring l2 R ≃ Algebra-Left-Module-Ring l2 R
  equiv-left-module-Algebra-Left-Module-Ring =
    ( algebra-left-module-left-module-Ring R ,
      is-equiv-algebra-left-module-left-module-Ring)
```

### Linear maps on left modules are equivalent to homomorphisms of algebras in the theory of left modules

```agda
hom-Algebra-Left-Module-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) →
  Algebra-Left-Module-Ring l2 R → Algebra-Left-Module-Ring l3 R →
  UU (l1 ⊔ l2 ⊔ l3)
hom-Algebra-Left-Module-Ring R =
  hom-Algebra
    ( signature-left-module-Ring R)
    ( algebraic-theory-left-module-Ring R)

linear-map-left-module-hom-Algebra-Left-Module-Ring :
  {l1 l2 l3 : Level} (R : Ring l1)
  (A : Algebra-Left-Module-Ring l2 R)
  (B : Algebra-Left-Module-Ring l3 R) →
  hom-Algebra-Left-Module-Ring R A B →
  linear-map-left-module-Ring R
    ( left-module-Algebra-Left-Module-Ring R A)
    ( left-module-Algebra-Left-Module-Ring R B)
linear-map-left-module-hom-Algebra-Left-Module-Ring
  R A B (φ , preserves-ops-φ) =
  ( φ ,
    ( λ x y →
      preserves-ops-φ add-operation-left-module-Ring (x ∷ y ∷ empty-tuple)) ,
    ( λ r x →
      preserves-ops-φ (mul-operation-left-module-Ring r) (x ∷ empty-tuple)))

module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  where

  hom-algebra-left-module-linear-map-left-module-Ring :
    linear-map-left-module-Ring R M N →
    hom-Algebra-Left-Module-Ring R
      ( algebra-left-module-left-module-Ring R M)
      ( algebra-left-module-left-module-Ring R N)
  hom-algebra-left-module-linear-map-left-module-Ring φ =
    ( map-linear-map-left-module-Ring R M N φ ,
      λ where
        zero-operation-left-module-Ring empty-tuple →
          is-zero-map-zero-linear-map-left-module-Ring R M N φ
        add-operation-left-module-Ring (x ∷ y ∷ empty-tuple) →
          is-additive-map-linear-map-left-module-Ring R M N φ x y
        neg-operation-left-module-Ring (x ∷ empty-tuple) →
          map-neg-linear-map-left-module-Ring R M N φ x
        (mul-operation-left-module-Ring r) (x ∷ empty-tuple) →
          is-homogeneous-map-linear-map-left-module-Ring R M N φ r x)

  is-equiv-hom-algebra-left-module-linear-map-left-module-Ring :
    is-equiv hom-algebra-left-module-linear-map-left-module-Ring
  is-equiv-hom-algebra-left-module-linear-map-left-module-Ring =
    is-equiv-is-invertible
      ( λ φ@(map-φ , preserves-ops-φ) →
        -- redoing this definition is easier than doing transport along
        -- is-retraction-left-module-Algebra-Left-Module-Ring
        ( map-φ ,
          ( λ x y →
            preserves-ops-φ
              ( add-operation-left-module-Ring)
              ( x ∷ y ∷ empty-tuple)) ,
        ( λ r x →
          preserves-ops-φ
            ( mul-operation-left-module-Ring r)
            ( x ∷ empty-tuple))))
      ( λ φ →
        eq-htpy-hom-Algebra
          ( signature-left-module-Ring R)
          ( algebraic-theory-left-module-Ring R)
          ( _)
          ( _)
          ( _)
          ( _)
          ( refl-htpy))
      ( λ φ → eq-htpy-linear-map-left-module-Ring R M N _ _ refl-htpy)

  equiv-linear-map-hom-algebra-Left-Module-Ring :
    linear-map-left-module-Ring R M N ≃
    hom-Algebra-Left-Module-Ring R
      ( algebra-left-module-left-module-Ring R M)
      ( algebra-left-module-left-module-Ring R N)
  equiv-linear-map-hom-algebra-Left-Module-Ring =
    ( hom-algebra-left-module-linear-map-left-module-Ring ,
      is-equiv-hom-algebra-left-module-linear-map-left-module-Ring)
```
