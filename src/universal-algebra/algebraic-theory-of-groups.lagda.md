# Algebraic theory of groups

```agda
module universal-algebra.algebraic-theory-of-groups where
```

<details><summary>Imports</summary>

```agda
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

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.isomorphisms-groups
open import group-theory.monoids

open import lists.tuples

open import univalent-combinatorics.standard-finite-types

open import universal-algebra.abstract-equations-over-signatures
open import universal-algebra.algebraic-theories
open import universal-algebra.algebraic-theory-of-monoids
open import universal-algebra.algebras
open import universal-algebra.extensions-signatures
open import universal-algebra.homomorphisms-of-algebras
open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
```

</details>

## Idea

There is an
{{#concept "algebraic theory of groups" Agda=algebraic-theory-Group}}. The type
of all such [algebras](universal-algebra.algebras.md) is
[equivalent](foundation-core.equivalences.md) to the type of
[groups](group-theory.groups.md).

## Definitions

### The algebra of groups

```agda
data operation-Group : UU lzero where
  operation-group-operation-Monoid : operation-Monoid → operation-Group
  inv-operation-Group : operation-Group

pattern mul-operation-Group =
  operation-group-operation-Monoid mul-operation-Monoid
pattern unit-operation-Group =
  operation-group-operation-Monoid unit-operation-Monoid

signature-Group : signature lzero
pr1 signature-Group = operation-Group
pr2 signature-Group (operation-group-operation-Monoid op) =
  arity-operation-signature signature-Monoid op
pr2 signature-Group inv-operation-Group = 1

data law-Group : UU lzero where
  law-group-law-Monoid : law-Monoid → law-Group
  left-inverse-law-law-Group : law-Group
  right-inverse-law-law-Group : law-Group

pattern associative-law-Group =
  law-group-law-Monoid associative-law-Monoid
pattern left-unit-law-law-Group =
  law-group-law-Monoid left-unit-law-law-Monoid
pattern right-unit-law-law-Group =
  law-group-law-Monoid right-unit-law-law-Monoid

extension-signature-monoid-Group :
  is-extension-of-signature signature-Monoid signature-Group
pr1 extension-signature-monoid-Group =
  operation-group-operation-Monoid
pr2 extension-signature-monoid-Group _ = refl

algebraic-theory-Group : Algebraic-Theory lzero signature-Group
pr1 algebraic-theory-Group = law-Group
pr2 algebraic-theory-Group =
  let
    var = var-term (zero-Fin 0)
    _*-term_ x y = op-term mul-operation-Group (x ∷ y ∷ empty-tuple)
    inv-term x = op-term inv-operation-Group (x ∷ empty-tuple)
    unit-term = op-term unit-operation-Group empty-tuple
  in
    λ where
      (law-group-law-Monoid law) →
        translation-abstract-equation
          ( signature-Monoid)
          ( signature-Group)
          ( extension-signature-monoid-Group)
          ( index-abstract-equation-Algebraic-Theory
            ( signature-Monoid)
            ( algebraic-theory-Monoid)
            ( law))
      left-inverse-law-law-Group →
        ( 1 ,
          inv-term var *-term var ,
          unit-term)
      right-inverse-law-law-Group →
        ( 1 ,
          var *-term inv-term var ,
          unit-term)

Algebra-Group : (l : Level) → UU (lsuc l)
Algebra-Group l = Algebra l signature-Group algebraic-theory-Group
```

## Properties

### Algebras in the theory of groups from groups

```agda
module _
  {l : Level}
  (G : Group l)
  where

  algebra-monoid-Group : Algebra-Monoid l
  algebra-monoid-Group =
    algebra-monoid-Monoid (monoid-Group G)

  is-model-set-Group : is-model-of-signature signature-Group (set-Group G)
  is-model-set-Group (operation-group-operation-Monoid op) =
    is-model-set-Monoid (monoid-Group G) op
  is-model-set-Group inv-operation-Group (x ∷ empty-tuple) =
    inv-Group G x

  model-set-Group : Model-Of-Signature l signature-Group
  model-set-Group = (set-Group G , is-model-set-Group)

  is-algebra-model-set-Group :
    is-algebra-Model-of-Signature
      ( signature-Group)
      ( algebraic-theory-Group)
      ( model-set-Group)
  is-algebra-model-set-Group associative-law-Group _ =
    associative-mul-Group G _ _ _
  is-algebra-model-set-Group left-unit-law-law-Group _ =
    left-unit-law-mul-Group G _
  is-algebra-model-set-Group right-unit-law-law-Group _ =
    right-unit-law-mul-Group G _
  is-algebra-model-set-Group left-inverse-law-law-Group _ =
    left-inverse-law-mul-Group G _
  is-algebra-model-set-Group right-inverse-law-law-Group _ =
    right-inverse-law-mul-Group G _

  algebra-group-Group : Algebra-Group l
  algebra-group-Group = (model-set-Group , is-algebra-model-set-Group)
```

### Groups from algebras in the theory of groups

```agda
module _
  {l : Level}
  (A@((set-A , model-A) , satisfies-A) : Algebra-Group l)
  where

  algebra-monoid-Algebra-Group : Algebra-Monoid l
  algebra-monoid-Algebra-Group =
    ( ( set-A , model-A ∘ operation-group-operation-Monoid) ,
      λ where
        associative-law-Monoid → satisfies-A associative-law-Group
        left-unit-law-law-Monoid → satisfies-A left-unit-law-law-Group
        right-unit-law-law-Monoid → satisfies-A right-unit-law-law-Group)

  monoid-Algebra-Group : Monoid l
  monoid-Algebra-Group = monoid-Algebra-Monoid algebra-monoid-Algebra-Group

  type-Algebra-Group : UU l
  type-Algebra-Group = type-Set set-A

  mul-Algebra-Group :
    type-Algebra-Group → type-Algebra-Group → type-Algebra-Group
  mul-Algebra-Group = mul-Monoid monoid-Algebra-Group

  unit-Algebra-Group : type-Algebra-Group
  unit-Algebra-Group = unit-Monoid monoid-Algebra-Group

  inv-Algebra-Group : type-Algebra-Group → type-Algebra-Group
  inv-Algebra-Group x = model-A inv-operation-Group (x ∷ empty-tuple)

  left-inverse-law-mul-Algebra-Group :
    (x : type-Algebra-Group) →
    mul-Algebra-Group (inv-Algebra-Group x) x ＝ unit-Algebra-Group
  left-inverse-law-mul-Algebra-Group x =
    satisfies-A left-inverse-law-law-Group (λ _ → x)

  right-inverse-law-mul-Algebra-Group :
    (x : type-Algebra-Group) →
    mul-Algebra-Group x (inv-Algebra-Group x) ＝ unit-Algebra-Group
  right-inverse-law-mul-Algebra-Group x =
    satisfies-A right-inverse-law-law-Group (λ _ → x)

  group-Algebra-Group : Group l
  group-Algebra-Group =
    group-is-group-Monoid
      ( monoid-Algebra-Group)
      ( inv-Algebra-Group ,
        left-inverse-law-mul-Algebra-Group ,
        right-inverse-law-mul-Algebra-Group)
```

### The type of groups is equivalent to the type of algebras in the theory of groups

```agda
abstract
  is-section-group-Algebra-Group :
    {l : Level} (A : Algebra-Group l) →
    algebra-group-Group (group-Algebra-Group A) ＝ A
  is-section-group-Algebra-Group ((set-A , models-A) , satisfies-A) =
    eq-type-subtype
      ( is-algebra-prop-Model-Of-Signature
        ( signature-Group)
        ( algebraic-theory-Group))
      ( eq-pair-eq-fiber
        ( eq-binary-htpy _ _
          ( λ where
            mul-operation-Group (x ∷ y ∷ empty-tuple) → refl
            unit-operation-Group empty-tuple → refl
            inv-operation-Group (x ∷ empty-tuple) → refl)))

  is-retraction-group-Algebra-Group :
    {l : Level} (G : Group l) →
    group-Algebra-Group (algebra-group-Group G) ＝ G
  is-retraction-group-Algebra-Group _ = refl

is-equiv-algebra-group-Group :
  {l : Level} → is-equiv (algebra-group-Group {l})
is-equiv-algebra-group-Group =
  is-equiv-is-invertible
    ( group-Algebra-Group)
    ( is-section-group-Algebra-Group)
    ( is-retraction-group-Algebra-Group)

equiv-group-Algebra-Group :
  {l : Level} → Group l ≃ Algebra-Group l
equiv-group-Algebra-Group =
  ( algebra-group-Group ,
    is-equiv-algebra-group-Group)
```

### Homomorphisms of groups are equivalent to homomorphisms of algebras in the theory of groups

```agda
hom-Algebra-Group :
  {l1 l2 : Level} → Algebra-Group l1 → Algebra-Group l2 → UU (l1 ⊔ l2)
hom-Algebra-Group = hom-Algebra signature-Group algebraic-theory-Group

hom-group-hom-Algebra-Group :
  {l1 l2 : Level} (G : Algebra-Group l1) (H : Algebra-Group l2) →
  hom-Algebra-Group G H →
  hom-Group (group-Algebra-Group G) (group-Algebra-Group H)
hom-group-hom-Algebra-Group G H (φ , preserves-ops-φ) =
  ( φ , preserves-ops-φ mul-operation-Group (_ ∷ _ ∷ empty-tuple))

module _
  {l1 l2 : Level}
  (G : Group l1)
  (H : Group l2)
  where

  hom-algebra-group-hom-Group :
    hom-Group G H →
    hom-Algebra-Group (algebra-group-Group G) (algebra-group-Group H)
  hom-algebra-group-hom-Group hom-φ@(φ , preserves-mul-φ) =
    ( φ ,
      λ where
        mul-operation-Group (x ∷ y ∷ empty-tuple) → preserves-mul-φ
        unit-operation-Group empty-tuple → preserves-unit-hom-Group G H hom-φ
        inv-operation-Group (x ∷ empty-tuple) →
          preserves-inv-hom-Group G H hom-φ)

  is-equiv-hom-algebra-group-hom-Group :
    is-equiv hom-algebra-group-hom-Group
  is-equiv-hom-algebra-group-hom-Group =
    is-equiv-is-invertible
      ( hom-group-hom-Algebra-Group
        ( algebra-group-Group G)
        ( algebra-group-Group H))
      ( λ φ →
        eq-htpy-hom-Algebra
          ( signature-Group)
          ( algebraic-theory-Group)
          ( algebra-group-Group G)
          ( algebra-group-Group H)
          ( _)
          ( φ)
          ( refl-htpy))
      ( λ φ → eq-htpy-hom-Group G H refl-htpy)

  equiv-hom-group-hom-Algebra-Group :
    hom-Group G H ≃
    hom-Algebra-Group (algebra-group-Group G) (algebra-group-Group H)
  equiv-hom-group-hom-Algebra-Group =
    ( hom-algebra-group-hom-Group ,
      is-equiv-hom-algebra-group-hom-Group)
```
