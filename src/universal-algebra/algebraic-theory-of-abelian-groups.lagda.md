# The algebraic theory of abelian groups

```agda
module universal-algebra.algebraic-theory-of-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
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
open import group-theory.groups
open import group-theory.homomorphisms-abelian-groups

open import lists.tuples

open import univalent-combinatorics.standard-finite-types

open import universal-algebra.algebraic-theories
open import universal-algebra.algebraic-theory-of-groups
open import universal-algebra.algebras
open import universal-algebra.homomorphisms-of-algebras
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
operation-Ab : UU lzero
operation-Ab = operation-Group

pattern zero-operation-Ab = unit-operation-Group
pattern add-operation-Ab = mul-operation-Group
pattern neg-operation-Ab = inv-operation-Group

signature-Ab : signature lzero
signature-Ab = signature-Group

data law-Ab : UU lzero where
  law-ab-law-Group : law-Group → law-Ab
  commutative-law-Ab : law-Ab

pattern associative-law-Ab = law-ab-law-Group associative-law-Group
pattern left-unit-law-law-Ab = law-ab-law-Group left-unit-law-law-Group
pattern right-unit-law-law-Ab = law-ab-law-Group right-unit-law-law-Group
pattern left-inverse-law-law-Ab = law-ab-law-Group left-inverse-law-law-Group
pattern right-inverse-law-law-Ab = law-ab-law-Group right-inverse-law-law-Group

algebraic-theory-Ab : Algebraic-Theory lzero signature-Ab
pr1 algebraic-theory-Ab = law-Ab
pr2 algebraic-theory-Ab (law-ab-law-Group law) =
  index-abstract-equation-Algebraic-Theory
    ( signature-Group)
    ( algebraic-theory-Group)
    ( law)
pr2 algebraic-theory-Ab commutative-law-Ab =
  let
    x-term = var-term (zero-Fin 1)
    y-term = var-term (one-Fin 1)
    add-term x y = op-term add-operation-Ab (x ∷ y ∷ empty-tuple)
  in
    ( 2 ,
      add-term x-term y-term ,
      add-term y-term x-term)

Algebra-Ab : (l : Level) → UU (lsuc l)
Algebra-Ab l = Algebra l signature-Ab algebraic-theory-Ab
```

## Properties

### Algebras in the theory of abelian groups from abelian groups

```agda
module _
  {l : Level}
  (G : Ab l)
  where

  algebra-group-Ab : Algebra-Group l
  algebra-group-Ab = algebra-group-Group (group-Ab G)

  model-set-Ab : Model-Of-Signature l signature-Ab
  model-set-Ab = model-set-Group (group-Ab G)

  is-algebra-model-set-Ab :
    is-algebra-Model-of-Signature
      ( signature-Ab)
      ( algebraic-theory-Ab)
      ( model-set-Ab)
  is-algebra-model-set-Ab (law-ab-law-Group law) =
    is-algebra-model-set-Group (group-Ab G) law
  is-algebra-model-set-Ab commutative-law-Ab _ = commutative-add-Ab G _ _

  algebra-ab-Ab : Algebra-Ab l
  algebra-ab-Ab = (model-set-Ab , is-algebra-model-set-Ab)
```

### Abelian groups from algebras in the theory of abelian groups

```agda
module _
  {l : Level}
  (A@((set-A , model-A) , satisfies-A) : Algebra-Ab l)
  where

  algebra-group-Algebra-Ab : Algebra-Group l
  algebra-group-Algebra-Ab =
    ((set-A , model-A) , satisfies-A ∘ law-ab-law-Group)

  group-Algebra-Ab : Group l
  group-Algebra-Ab = group-Algebra-Group algebra-group-Algebra-Ab

  type-Algebra-Ab : UU l
  type-Algebra-Ab = type-Set set-A

  add-Algebra-Ab : type-Algebra-Ab → type-Algebra-Ab → type-Algebra-Ab
  add-Algebra-Ab = mul-Group group-Algebra-Ab

  commutative-add-Algebra-Ab :
    (x y : type-Algebra-Ab) → add-Algebra-Ab x y ＝ add-Algebra-Ab y x
  commutative-add-Algebra-Ab x y =
    satisfies-A commutative-law-Ab (component-tuple 2 (y ∷ x ∷ empty-tuple))

  ab-Algebra-Ab : Ab l
  ab-Algebra-Ab = (group-Algebra-Ab , commutative-add-Algebra-Ab)
```

### The type of abelian groups is equivalent to the type of algebras in the algebraic theory of abelian groups

```agda
abstract
  is-section-ab-Algebra-Ab :
    {l : Level} (A : Algebra-Ab l) → algebra-ab-Ab (ab-Algebra-Ab A) ＝ A
  is-section-ab-Algebra-Ab A =
    eq-type-subtype
      ( is-algebra-prop-Model-Of-Signature
        ( signature-Ab)
        ( algebraic-theory-Ab))
      ( ap
        ( model-Algebra signature-Group algebraic-theory-Group)
        ( is-section-group-Algebra-Group (algebra-group-Algebra-Ab A)))

  is-retraction-ab-Algebra-Ab :
    {l : Level} (G : Ab l) → ab-Algebra-Ab (algebra-ab-Ab G) ＝ G
  is-retraction-ab-Algebra-Ab _ = refl

is-equiv-algebra-ab-Ab :
  {l : Level} → is-equiv (algebra-ab-Ab {l})
is-equiv-algebra-ab-Ab =
  is-equiv-is-invertible
    ( ab-Algebra-Ab)
    ( is-section-ab-Algebra-Ab)
    ( is-retraction-ab-Algebra-Ab)

equiv-ab-Algebra-Ab :
  {l : Level} → Ab l ≃ Algebra-Ab l
equiv-ab-Algebra-Ab = (algebra-ab-Ab , is-equiv-algebra-ab-Ab)
```

### Homomorphisms of abelian groups are equivalent to homomorphisms of algebras in the theory of abelian groups

```agda
hom-Algebra-Ab : {l1 l2 : Level} → Algebra-Ab l1 → Algebra-Ab l2 → UU (l1 ⊔ l2)
hom-Algebra-Ab = hom-Algebra signature-Ab algebraic-theory-Ab

hom-ab-hom-Algebra-Ab :
  {l1 l2 : Level} (G : Algebra-Ab l1) (H : Algebra-Ab l2) →
  hom-Algebra-Ab G H → hom-Ab (ab-Algebra-Ab G) (ab-Algebra-Ab H)
hom-ab-hom-Algebra-Ab G H =
  hom-group-hom-Algebra-Group
    ( algebra-group-Algebra-Ab G)
    ( algebra-group-Algebra-Ab H)

module _
  {l1 l2 : Level}
  (G : Ab l1)
  (H : Ab l2)
  where

  equiv-hom-ab-hom-Algebra-Ab :
    hom-Ab G H ≃ hom-Algebra-Ab (algebra-ab-Ab G) (algebra-ab-Ab H)
  equiv-hom-ab-hom-Algebra-Ab =
    equiv-hom-group-hom-Algebra-Group (group-Ab G) (group-Ab H)

  hom-algebra-ab-hom-Ab :
    hom-Ab G H → hom-Algebra-Ab (algebra-ab-Ab G) (algebra-ab-Ab H)
  hom-algebra-ab-hom-Ab = map-equiv equiv-hom-ab-hom-Algebra-Ab
```
