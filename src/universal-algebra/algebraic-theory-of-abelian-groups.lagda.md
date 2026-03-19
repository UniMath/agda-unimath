# The algebraic theory of abelian groups

```agda
{-# OPTIONS --lossy-unification #-}

module universal-algebra.algebraic-theory-of-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups

open import lists.tuples

open import univalent-combinatorics.standard-finite-types

open import universal-algebra.algebraic-theories
open import universal-algebra.algebraic-theory-of-groups
open import universal-algebra.algebras
open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
```

</details>

## Idea

There is an
{{#concept "algebraic theory of abelian groups" Agda=algebraic-theory-Ab}}. The
type of all such [algebras](universal-algebra.algebras.md) is
[equivalent](foundation-core.equivalences.md) to the type of
[abelian groups](group-theory.abelian-groups.md).

## Definition

```agda
data ab-laws : UU lzero where
  ab-law-group-law : group-laws → ab-laws
  commutative-add-ab-law : ab-laws

algebraic-theory-Ab : Algebraic-Theory lzero group-signature
pr1 algebraic-theory-Ab = ab-laws
pr2 algebraic-theory-Ab (ab-law-group-law law) =
  pr2 algebraic-theory-Group law
pr2 algebraic-theory-Ab commutative-add-ab-law =
  ( 2 ,
    op-term
      ( mul-group-op)
      ( var-term (zero-Fin 1) ∷ var-term (one-Fin 1) ∷ empty-tuple) ,
    op-term
      ( mul-group-op)
      ( var-term (one-Fin 1) ∷ var-term (zero-Fin 1) ∷ empty-tuple))

Algebra-Ab : (l : Level) → UU (lsuc l)
Algebra-Ab l = Algebra l group-signature algebraic-theory-Ab
```

## Properties

### The algebra of abelian groups is equivalent to the type of abelian groups

```agda
module _
  {l : Level}
  (G : Ab l)
  where

  is-model-algebra-ab-Ab : is-model-of-signature group-signature (set-Ab G)
  is-model-algebra-ab-Ab =
    is-model-set-Algebra
      ( group-signature)
      ( algebraic-theory-Group)
      ( (algebra-group-Group (group-Ab G)))

  model-of-signature-algebra-ab-Ab :
    Model-Of-Signature l group-signature
  model-of-signature-algebra-ab-Ab =
    ( set-Ab G , is-model-algebra-ab-Ab)

  is-algebra-model-algebra-ab-Ab :
    is-algebra-Model-of-Signature
      ( group-signature)
      ( algebraic-theory-Ab)
      ( model-of-signature-algebra-ab-Ab)
  is-algebra-model-algebra-ab-Ab (ab-law-group-law group-law) xs =
    is-algebra-model-Algebra
      ( group-signature)
      ( algebraic-theory-Group)
      ( algebra-group-Group (group-Ab G))
      ( group-law)
      ( xs)
  is-algebra-model-algebra-ab-Ab commutative-add-ab-law xs =
    commutative-add-Ab G _ _

  algebra-ab-Ab : Algebra-Ab l
  algebra-ab-Ab =
    ((set-Ab G , is-model-algebra-ab-Ab) , is-algebra-model-algebra-ab-Ab)

module _
  {l : Level}
  (A : Algebra-Ab l)
  where

  group-Algebra-Ab : Group l
  group-Algebra-Ab =
    group-algebra-Group
      ( ( set-Algebra group-signature algebraic-theory-Ab A ,
          is-model-set-Algebra group-signature algebraic-theory-Ab A) ,
        ( ( is-algebra-model-Algebra group-signature algebraic-theory-Ab A) ∘
          ( ab-law-group-law)))

  type-Algebra-Ab : UU l
  type-Algebra-Ab = type-Group group-Algebra-Ab

  add-Algebra-Ab : type-Algebra-Ab → type-Algebra-Ab → type-Algebra-Ab
  add-Algebra-Ab = mul-Group group-Algebra-Ab

  commutative-add-Algebra-Ab :
    (x y : type-Algebra-Ab) → add-Algebra-Ab x y ＝ add-Algebra-Ab y x
  commutative-add-Algebra-Ab x y =
    is-algebra-model-Algebra
      ( group-signature)
      ( algebraic-theory-Ab)
      ( A)
      ( commutative-add-ab-law)
      ( component-tuple 2 (y ∷ x ∷ empty-tuple))

  ab-Algebra-Ab : Ab l
  ab-Algebra-Ab =
    ( group-Algebra-Ab , commutative-add-Algebra-Ab)
```
