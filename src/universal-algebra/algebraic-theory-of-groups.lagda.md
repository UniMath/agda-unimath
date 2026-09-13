# Algebraic theory of groups

```agda
module universal-algebra.algebraic-theory-of-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups

open import lists.equivalence-tuples-finite-sequences
open import lists.tuples

open import univalent-combinatorics.classical-finite-types
open import univalent-combinatorics.standard-finite-types

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras
open import universal-algebra.homomorphisms-of-algebras
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
data group-ops : UU lzero where
  unit-group-op mul-group-op inv-group-op : group-ops

group-signature : signature lzero
pr1 group-signature = group-ops
pr2 group-signature unit-group-op = 0
pr2 group-signature mul-group-op = 2
pr2 group-signature inv-group-op = 1

data group-laws : UU lzero where
  associative-group-laws : group-laws
  invl-group-laws : group-laws
  invr-group-laws : group-laws
  idl-l-group-laws : group-laws
  idr-group-laws : group-laws

algebraic-theory-Group : Algebraic-Theory lzero group-signature
pr1 algebraic-theory-Group = group-laws
pr2 algebraic-theory-Group =
  let
    _*-term_ :
      {k : ℕ} →
      term group-signature k → term group-signature k → term group-signature k
    _*-term_ x y =
      op-term
        ( mul-group-op)
        ( x ∷ y ∷ empty-tuple)
    inv-term x = op-term inv-group-op (x ∷ empty-tuple)
    unit-term = op-term unit-group-op empty-tuple
    var : (i : ℕ) {k : ℕ} → {le-ℕ i k} → term group-signature k
    var i {k} {i<k} = var-term (standard-classical-Fin k (i , i<k))
  in
    λ where
      associative-group-laws →
        ( 3 ,
          (var 0 *-term var 1) *-term var 2 ,
          var 0 *-term (var 1 *-term var 2))
      invl-group-laws →
        ( 1 ,
          inv-term (var 0) *-term var 0 ,
          unit-term)
      invr-group-laws →
        ( 1 ,
          var 0 *-term inv-term (var 0) ,
          unit-term)
      idl-l-group-laws →
        ( 1 ,
          unit-term *-term var 0 ,
          var 0)
      idr-group-laws →
        ( 1 ,
          var 0 *-term unit-term ,
          var 0)

algebra-Group : (l : Level) → UU (lsuc l)
algebra-Group l = Algebra l group-signature algebraic-theory-Group
```

## Properties

### The algebra of groups is equivalent to the type of groups

```agda
group-algebra-Group :
  {l : Level} → algebra-Group l → Group l
group-algebra-Group ((A-Set , models-A) , satisfies-A) =
  let
    mul-A x y = models-A mul-group-op (x ∷ y ∷ empty-tuple)
    inv-A x = models-A inv-group-op (x ∷ empty-tuple)
    unit-A = models-A unit-group-op empty-tuple
    associative-mul-A x y z =
      satisfies-A
        ( associative-group-laws)
        ( fin-sequence-tuple 3 (z ∷ y ∷ x ∷ empty-tuple))
    left-unit-law-mul-A x =
      satisfies-A idl-l-group-laws (λ _ → x)
    right-unit-law-mul-A x =
      satisfies-A idr-group-laws (λ _ → x)
    left-inv-law-mul-A x =
      satisfies-A invl-group-laws (λ _ → x)
    right-inv-law-mul-A x =
      satisfies-A invr-group-laws (λ _ → x)
  in
    ( ( A-Set , mul-A , associative-mul-A) ,
      ( unit-A , left-unit-law-mul-A , right-unit-law-mul-A) ,
      ( inv-A , left-inv-law-mul-A , right-inv-law-mul-A))

algebra-group-Group :
  {l : Level} → Group l → algebra-Group l
algebra-group-Group G =
  let
    fin : (i : ℕ) (k : ℕ) → {le-ℕ i k} → Fin k
    fin i k {i<k} = standard-classical-Fin k (i , i<k)
  in
    ( ( set-Group G ,
        λ where
          mul-group-op (x ∷ y ∷ empty-tuple) → mul-Group G x y
          inv-group-op (x ∷ empty-tuple) → inv-Group G x
          unit-group-op _ → unit-Group G) ,
      λ where
        associative-group-laws xs →
          associative-mul-Group G (xs (fin 0 3)) (xs (fin 1 3)) (xs (fin 2 3))
        invl-group-laws xs →
          left-inverse-law-mul-Group G (xs (fin 0 1))
        invr-group-laws xs →
          right-inverse-law-mul-Group G (xs (fin 0 1))
        idl-l-group-laws xs →
          left-unit-law-mul-Group G (xs (fin 0 1))
        idr-group-laws xs →
          right-unit-law-mul-Group G (xs (fin 0 1)))

abstract
  equiv-group-algebra-Group :
    {l : Level} → algebra-Group l ≃ Group l
  pr1 equiv-group-algebra-Group = group-algebra-Group
  pr1 (pr1 (pr2 equiv-group-algebra-Group)) = algebra-group-Group
  pr2 (pr1 (pr2 equiv-group-algebra-Group)) G =
    eq-type-subtype
      ( is-group-prop-Semigroup)
      ( refl)
  pr1 (pr2 (pr2 equiv-group-algebra-Group)) = algebra-group-Group
  pr2 (pr2 (pr2 equiv-group-algebra-Group)) A =
    eq-type-subtype
      ( is-algebra-prop-Model-Of-Signature
        ( group-signature)
        ( algebraic-theory-Group))
      ( eq-pair-eq-fiber
        ( eq-htpy
          λ where
            unit-group-op → eq-htpy (λ where empty-tuple → refl)
            mul-group-op → eq-htpy (λ where (x ∷ y ∷ empty-tuple) → refl)
            inv-group-op → eq-htpy (λ where (x ∷ empty-tuple) → refl)))
```

### Homomorphisms of groups are homomorphisms of the algebra of groups, and vice versa

```agda
hom-algebra-Group :
  {l1 l2 : Level} → algebra-Group l1 → algebra-Group l2 → UU (l1 ⊔ l2)
hom-algebra-Group =
  hom-Algebra group-signature algebraic-theory-Group

hom-group-hom-algebra-Group :
  {l1 l2 : Level} (G : algebra-Group l1) (H : algebra-Group l2) →
  hom-algebra-Group G H →
  hom-Group (group-algebra-Group G) (group-algebra-Group H)
hom-group-hom-algebra-Group G H (f , K) =
  ( f , λ {x} {y} → K mul-group-op (x ∷ y ∷ empty-tuple))

hom-algebra-group-hom-Group :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) →
  hom-Group G H →
  hom-algebra-Group (algebra-group-Group G) (algebra-group-Group H)
hom-algebra-group-hom-Group G H (f , K) =
  ( f ,
    λ where
      unit-group-op empty-tuple → preserves-unit-hom-Group G H (f , K)
      mul-group-op (x ∷ y ∷ empty-tuple) → K {x} {y}
      inv-group-op (x ∷ empty-tuple) → preserves-inv-hom-Group G H (f , K))
```
