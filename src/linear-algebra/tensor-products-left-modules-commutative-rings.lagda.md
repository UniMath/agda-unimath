# Tensor products of left modules over commutative rings

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.tensor-products-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.propositional-truncation-binary-relations
open import foundation.propositional-truncations
open import foundation.set-quotients
open import foundation.universe-levels

open import linear-algebra.bilinear-maps-left-modules-commutative-rings
open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.linear-maps-left-modules-commutative-rings

open import lists.tuples

open import universal-algebra.algebraic-theory-of-left-modules-commutative-rings
open import universal-algebra.algebraic-theory-of-left-modules-rings
open import universal-algebra.algebras
open import universal-algebra.congruences
open import universal-algebra.freely-generated-algebras
open import universal-algebra.quotient-algebras
```

</details>

## Idea

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (N : left-module-Commutative-Ring l3 R)
  where

  free-algebra-tensor-product-left-module-Commutative-Ring :
    Algebra-Left-Module-Commutative-Ring (l1 ⊔ l2 ⊔ l3) R
  free-algebra-tensor-product-left-module-Commutative-Ring =
    free-Algebra
      ( signature-left-module-Commutative-Ring R)
      ( algebraic-theory-left-module-Commutative-Ring R)
      ( ( type-left-module-Commutative-Ring R M) ×
        ( type-left-module-Commutative-Ring R N))

  free-left-module-tensor-product-left-module-Commutative-Ring :
    left-module-Commutative-Ring (l1 ⊔ l2 ⊔ l3) R
  free-left-module-tensor-product-left-module-Commutative-Ring =
    left-module-Algebra-Left-Module-Commutative-Ring
      ( R)
      ( free-algebra-tensor-product-left-module-Commutative-Ring)

  type-free-algebra-tensor-product-left-module-Commutative-Ring :
    UU (l1 ⊔ l2 ⊔ l3)
  type-free-algebra-tensor-product-left-module-Commutative-Ring =
    type-left-module-Commutative-Ring
      ( R)
      ( free-left-module-tensor-product-left-module-Commutative-Ring)

  add-free-algebra-tensor-product-left-module-Commutative-Ring :
    type-free-algebra-tensor-product-left-module-Commutative-Ring →
    type-free-algebra-tensor-product-left-module-Commutative-Ring →
    type-free-algebra-tensor-product-left-module-Commutative-Ring
  add-free-algebra-tensor-product-left-module-Commutative-Ring =
    add-left-module-Commutative-Ring
      ( R)
      ( free-left-module-tensor-product-left-module-Commutative-Ring)

  mul-free-algebra-tensor-product-left-module-Commutative-Ring :
    type-Commutative-Ring R →
    type-free-algebra-tensor-product-left-module-Commutative-Ring →
    type-free-algebra-tensor-product-left-module-Commutative-Ring
  mul-free-algebra-tensor-product-left-module-Commutative-Ring =
    mul-left-module-Commutative-Ring
      ( R)
      ( free-left-module-tensor-product-left-module-Commutative-Ring)

  neg-free-algebra-tensor-product-left-module-Commutative-Ring :
    type-free-algebra-tensor-product-left-module-Commutative-Ring →
    type-free-algebra-tensor-product-left-module-Commutative-Ring
  neg-free-algebra-tensor-product-left-module-Commutative-Ring =
    neg-left-module-Commutative-Ring
      ( R)
      ( free-left-module-tensor-product-left-module-Commutative-Ring)

  zero-free-algebra-tensor-product-left-module-Commutative-Ring :
    type-free-algebra-tensor-product-left-module-Commutative-Ring
  zero-free-algebra-tensor-product-left-module-Commutative-Ring =
    zero-left-module-Commutative-Ring
      ( R)
      ( free-left-module-tensor-product-left-module-Commutative-Ring)

  in-free-algebra-tensor-product-left-module-Commutative-Ring :
    type-left-module-Commutative-Ring R M →
    type-left-module-Commutative-Ring R N →
    type-free-algebra-tensor-product-left-module-Commutative-Ring
  in-free-algebra-tensor-product-left-module-Commutative-Ring m n =
    in-generator-free-Algebra
      ( signature-left-module-Commutative-Ring R)
      ( algebraic-theory-left-module-Commutative-Ring R)
      ( ( type-left-module-Commutative-Ring R M) ×
        ( type-left-module-Commutative-Ring R N))
      ( m , n)

  data rel-tensor-product-left-module-Commutative-Ring :
    Relation
      ( l1 ⊔ l2 ⊔ l3)
      ( type-free-algebra-tensor-product-left-module-Commutative-Ring) where

    refl-rel-tensor-product-left-module-Commutative-Ring :
      is-reflexive rel-tensor-product-left-module-Commutative-Ring

    symmetric-rel-tensor-product-left-module-Commutative-Ring :
      is-symmetric rel-tensor-product-left-module-Commutative-Ring

    transitive-rel-tensor-product-left-module-Commutative-Ring :
      is-transitive rel-tensor-product-left-module-Commutative-Ring

    left-additive-rel-tensor-product-left-module-Commutative-Ring :
      (m m' : type-left-module-Commutative-Ring R M)
      (n : type-left-module-Commutative-Ring R N) →
      rel-tensor-product-left-module-Commutative-Ring
        ( add-free-algebra-tensor-product-left-module-Commutative-Ring
          ( in-free-algebra-tensor-product-left-module-Commutative-Ring m n)
          ( in-free-algebra-tensor-product-left-module-Commutative-Ring m' n))
        ( in-free-algebra-tensor-product-left-module-Commutative-Ring
          ( add-left-module-Commutative-Ring R M m m')
          ( n))

    right-additive-rel-tensor-product-left-module-Commutative-Ring :
      (m : type-left-module-Commutative-Ring R M)
      (n n' : type-left-module-Commutative-Ring R N) →
      rel-tensor-product-left-module-Commutative-Ring
        ( add-free-algebra-tensor-product-left-module-Commutative-Ring
          ( in-free-algebra-tensor-product-left-module-Commutative-Ring m n)
          ( in-free-algebra-tensor-product-left-module-Commutative-Ring m n'))
        ( in-free-algebra-tensor-product-left-module-Commutative-Ring
          ( m)
          ( add-left-module-Commutative-Ring R N n n'))

    left-homogeneous-rel-tensor-product-left-module-Commutative-Ring :
      (r : type-Commutative-Ring R)
      (m : type-left-module-Commutative-Ring R M)
      (n : type-left-module-Commutative-Ring R N) →
      rel-tensor-product-left-module-Commutative-Ring
        ( mul-free-algebra-tensor-product-left-module-Commutative-Ring
          ( r)
          ( in-free-algebra-tensor-product-left-module-Commutative-Ring m n))
        ( in-free-algebra-tensor-product-left-module-Commutative-Ring
          ( mul-left-module-Commutative-Ring R M r m)
          ( n))

    right-homogeneous-rel-tensor-product-left-module-Commutative-Ring :
      (r : type-Commutative-Ring R)
      (m : type-left-module-Commutative-Ring R M)
      (n : type-left-module-Commutative-Ring R N) →
      rel-tensor-product-left-module-Commutative-Ring
        ( mul-free-algebra-tensor-product-left-module-Commutative-Ring
          ( r)
          ( in-free-algebra-tensor-product-left-module-Commutative-Ring m n))
        ( in-free-algebra-tensor-product-left-module-Commutative-Ring
          ( m)
          ( mul-left-module-Commutative-Ring R N r n))

    ap-add-rel-tensor-product-left-module-Commutative-Ring :
      (x x' y y' :
        type-free-algebra-tensor-product-left-module-Commutative-Ring) →
      rel-tensor-product-left-module-Commutative-Ring x x' →
      rel-tensor-product-left-module-Commutative-Ring y y' →
      rel-tensor-product-left-module-Commutative-Ring
        ( add-free-algebra-tensor-product-left-module-Commutative-Ring x y)
        ( add-free-algebra-tensor-product-left-module-Commutative-Ring x' y')

    ap-mul-rel-tensor-product-left-module-Commutative-Ring :
      (r : type-Commutative-Ring R)
      (x x' : type-free-algebra-tensor-product-left-module-Commutative-Ring) →
      rel-tensor-product-left-module-Commutative-Ring x x' →
      rel-tensor-product-left-module-Commutative-Ring
        ( mul-free-algebra-tensor-product-left-module-Commutative-Ring r x)
        ( mul-free-algebra-tensor-product-left-module-Commutative-Ring r x')

    ap-neg-rel-tensor-product-left-module-Commutative-Ring :
      (x x' : type-free-algebra-tensor-product-left-module-Commutative-Ring) →
      rel-tensor-product-left-module-Commutative-Ring x x' →
      rel-tensor-product-left-module-Commutative-Ring
        ( neg-free-algebra-tensor-product-left-module-Commutative-Ring x)
        ( neg-free-algebra-tensor-product-left-module-Commutative-Ring x')

  equivalence-relation-free-algebra-tensor-product-left-module-Commutative-Ring :
    equivalence-relation
      ( l1 ⊔ l2 ⊔ l3)
      ( type-free-algebra-tensor-product-left-module-Commutative-Ring)
  equivalence-relation-free-algebra-tensor-product-left-module-Commutative-Ring =
    ( trunc-prop-Relation
        ( rel-tensor-product-left-module-Commutative-Ring) ,
      reflexive-trunc-prop-Relation
        ( rel-tensor-product-left-module-Commutative-Ring)
        ( refl-rel-tensor-product-left-module-Commutative-Ring) ,
      symmetric-trunc-prop-Relation
        ( rel-tensor-product-left-module-Commutative-Ring)
        ( symmetric-rel-tensor-product-left-module-Commutative-Ring) ,
      transitive-trunc-prop-Relation
        ( rel-tensor-product-left-module-Commutative-Ring)
        ( transitive-rel-tensor-product-left-module-Commutative-Ring))

  abstract
    preserves-operations-equivalence-relation-free-algebra-tensor-product-left-module-Commutative-Ring :
      preserves-operations-equivalence-relation-Algebra
        ( signature-left-module-Commutative-Ring R)
        ( algebraic-theory-left-module-Commutative-Ring R)
        ( free-algebra-tensor-product-left-module-Commutative-Ring)
        ( equivalence-relation-free-algebra-tensor-product-left-module-Commutative-Ring)
    preserves-operations-equivalence-relation-free-algebra-tensor-product-left-module-Commutative-Ring
      add-operation-left-module-Ring
      {x ∷ y ∷ empty-tuple} {x' ∷ y' ∷ empty-tuple} (x~x' , y~y' , _) =
      map-binary-trunc-Prop
        ( ap-add-rel-tensor-product-left-module-Commutative-Ring x x' y y')
        ( x~x')
        ( y~y')
    preserves-operations-equivalence-relation-free-algebra-tensor-product-left-module-Commutative-Ring
      (mul-operation-left-module-Ring r) {x ∷ empty-tuple} {x' ∷ empty-tuple}
      (x~x' , _) =
      map-trunc-Prop
        ( ap-mul-rel-tensor-product-left-module-Commutative-Ring r x x')
        ( x~x')
    preserves-operations-equivalence-relation-free-algebra-tensor-product-left-module-Commutative-Ring
      neg-operation-left-module-Ring {x ∷ empty-tuple} {x' ∷ empty-tuple}
      (x~x' , _) =
      map-trunc-Prop
        ( ap-neg-rel-tensor-product-left-module-Commutative-Ring x x')
        ( x~x')
    preserves-operations-equivalence-relation-free-algebra-tensor-product-left-module-Commutative-Ring
      zero-operation-left-module-Ring {empty-tuple} {empty-tuple} _ =
      unit-trunc-Prop
        ( refl-rel-tensor-product-left-module-Commutative-Ring
          ( zero-free-algebra-tensor-product-left-module-Commutative-Ring))

  congruence-free-algebra-tensor-product-left-module-Commutative-Ring :
    congruence-Algebra
      ( l1 ⊔ l2 ⊔ l3)
      ( signature-left-module-Commutative-Ring R)
      ( algebraic-theory-left-module-Commutative-Ring R)
      ( free-algebra-tensor-product-left-module-Commutative-Ring)
  congruence-free-algebra-tensor-product-left-module-Commutative-Ring =
    ( equivalence-relation-free-algebra-tensor-product-left-module-Commutative-Ring ,
      preserves-operations-equivalence-relation-free-algebra-tensor-product-left-module-Commutative-Ring)

  opaque
    algebra-tensor-product-left-module-Commutative-Ring :
      Algebra-Left-Module-Commutative-Ring (l1 ⊔ l2 ⊔ l3) R
    algebra-tensor-product-left-module-Commutative-Ring =
      quotient-Algebra
        ( signature-left-module-Commutative-Ring R)
        ( algebraic-theory-left-module-Commutative-Ring R)
        ( free-algebra-tensor-product-left-module-Commutative-Ring)
        ( congruence-free-algebra-tensor-product-left-module-Commutative-Ring)

    tensor-product-left-module-Commutative-Ring :
      left-module-Commutative-Ring (l1 ⊔ l2 ⊔ l3) R
    tensor-product-left-module-Commutative-Ring =
      left-module-Algebra-Left-Module-Commutative-Ring
        ( R)
        ( algebra-tensor-product-left-module-Commutative-Ring)

  type-tensor-product-left-module-Commutative-Ring : UU (l1 ⊔ l2 ⊔ l3)
  type-tensor-product-left-module-Commutative-Ring =
    type-left-module-Commutative-Ring
      ( R)
      ( tensor-product-left-module-Commutative-Ring)

  add-tensor-product-left-module-Commutative-Ring :
    type-tensor-product-left-module-Commutative-Ring →
    type-tensor-product-left-module-Commutative-Ring →
    type-tensor-product-left-module-Commutative-Ring
  add-tensor-product-left-module-Commutative-Ring =
    add-left-module-Commutative-Ring
      ( R)
      ( tensor-product-left-module-Commutative-Ring)

  mul-tensor-product-left-module-Commutative-Ring :
    type-Commutative-Ring R →
    type-tensor-product-left-module-Commutative-Ring →
    type-tensor-product-left-module-Commutative-Ring
  mul-tensor-product-left-module-Commutative-Ring =
    mul-left-module-Commutative-Ring
      ( R)
      ( tensor-product-left-module-Commutative-Ring)

  opaque
    unfolding tensor-product-left-module-Commutative-Ring

    in-type-free-algebra-tensor-product-left-module-Commutative-Ring :
      type-free-algebra-tensor-product-left-module-Commutative-Ring →
      type-tensor-product-left-module-Commutative-Ring
    in-type-free-algebra-tensor-product-left-module-Commutative-Ring =
      quotient-map
        ( equivalence-relation-free-algebra-tensor-product-left-module-Commutative-Ring)

    in-tensor-product-left-module-Commutative-Ring :
      type-left-module-Commutative-Ring R M →
      type-left-module-Commutative-Ring R N →
      type-tensor-product-left-module-Commutative-Ring
    in-tensor-product-left-module-Commutative-Ring m n =
      in-type-free-algebra-tensor-product-left-module-Commutative-Ring
        ( in-free-algebra-tensor-product-left-module-Commutative-Ring m n)

  abstract opaque
    unfolding in-tensor-product-left-module-Commutative-Ring

    eq-in-type-free-tensor-product-left-module-Commutative-Ring :
      {x y : type-free-algebra-tensor-product-left-module-Commutative-Ring} →
      rel-tensor-product-left-module-Commutative-Ring x y →
      in-type-free-algebra-tensor-product-left-module-Commutative-Ring x ＝
      in-type-free-algebra-tensor-product-left-module-Commutative-Ring y
    eq-in-type-free-tensor-product-left-module-Commutative-Ring x~y =
      apply-effectiveness-quotient-map'
        ( equivalence-relation-free-algebra-tensor-product-left-module-Commutative-Ring)
        ( unit-trunc-Prop x~y)

    compute-add-tensor-product-left-module-Commutative-Ring :
      (x y :
        type-free-algebra-tensor-product-left-module-Commutative-Ring) →
      add-tensor-product-left-module-Commutative-Ring
        ( in-type-free-algebra-tensor-product-left-module-Commutative-Ring x)
        ( in-type-free-algebra-tensor-product-left-module-Commutative-Ring y) ＝
      in-type-free-algebra-tensor-product-left-module-Commutative-Ring
        ( add-free-algebra-tensor-product-left-module-Commutative-Ring x y)
    compute-add-tensor-product-left-module-Commutative-Ring x y =
      compute-is-model-quotient-Algebra
        ( signature-left-module-Commutative-Ring R)
        ( algebraic-theory-left-module-Commutative-Ring R)
        ( free-algebra-tensor-product-left-module-Commutative-Ring)
        ( congruence-free-algebra-tensor-product-left-module-Commutative-Ring)
        ( add-operation-left-module-Ring)
        ( x ∷ y ∷ empty-tuple)

    compute-mul-tensor-product-left-module-Commutative-Ring :
      (r : type-Commutative-Ring R)
      (x : type-free-algebra-tensor-product-left-module-Commutative-Ring) →
      mul-tensor-product-left-module-Commutative-Ring
        ( r)
        ( in-type-free-algebra-tensor-product-left-module-Commutative-Ring x) ＝
      in-type-free-algebra-tensor-product-left-module-Commutative-Ring
        ( mul-free-algebra-tensor-product-left-module-Commutative-Ring r x)
    compute-mul-tensor-product-left-module-Commutative-Ring r x =
      compute-is-model-quotient-Algebra
        ( signature-left-module-Commutative-Ring R)
        ( algebraic-theory-left-module-Commutative-Ring R)
        ( free-algebra-tensor-product-left-module-Commutative-Ring)
        ( congruence-free-algebra-tensor-product-left-module-Commutative-Ring)
        ( mul-operation-left-module-Ring r)
        ( x ∷ empty-tuple)

    is-left-additive-in-tensor-product-left-module-Commutative-Ring :
      (n : type-left-module-Commutative-Ring R N)
      (m m' : type-left-module-Commutative-Ring R M) →
      in-tensor-product-left-module-Commutative-Ring
        ( add-left-module-Commutative-Ring R M m m')
        ( n) ＝
      add-tensor-product-left-module-Commutative-Ring
        ( in-tensor-product-left-module-Commutative-Ring m n)
        ( in-tensor-product-left-module-Commutative-Ring m' n)
    is-left-additive-in-tensor-product-left-module-Commutative-Ring n m m' =
      inv
        ( ( compute-add-tensor-product-left-module-Commutative-Ring _ _) ∙
          ( eq-in-type-free-tensor-product-left-module-Commutative-Ring
            ( left-additive-rel-tensor-product-left-module-Commutative-Ring
              ( m)
              ( m')
              ( n))))

    is-left-homogeneous-in-tensor-product-left-module-Commutative-Ring :
      (n : type-left-module-Commutative-Ring R N)
      (r : type-Commutative-Ring R)
      (m : type-left-module-Commutative-Ring R M) →
      in-tensor-product-left-module-Commutative-Ring
        ( mul-left-module-Commutative-Ring R M r m)
        ( n) ＝
      mul-tensor-product-left-module-Commutative-Ring r
        ( in-tensor-product-left-module-Commutative-Ring m n)
    is-left-homogeneous-in-tensor-product-left-module-Commutative-Ring n r m =
      inv
        ( ( compute-mul-tensor-product-left-module-Commutative-Ring _ _) ∙
          ( eq-in-type-free-tensor-product-left-module-Commutative-Ring
            ( left-homogeneous-rel-tensor-product-left-module-Commutative-Ring
              ( r)
              ( m)
              ( n))))

    is-right-additive-in-tensor-product-left-module-Commutative-Ring :
      (m : type-left-module-Commutative-Ring R M)
      (n n' : type-left-module-Commutative-Ring R N) →
      in-tensor-product-left-module-Commutative-Ring
        ( m)
        ( add-left-module-Commutative-Ring R N n n') ＝
      add-tensor-product-left-module-Commutative-Ring
        ( in-tensor-product-left-module-Commutative-Ring m n)
        ( in-tensor-product-left-module-Commutative-Ring m n')
    is-right-additive-in-tensor-product-left-module-Commutative-Ring m n n' =
      inv
        ( ( compute-add-tensor-product-left-module-Commutative-Ring _ _) ∙
          ( eq-in-type-free-tensor-product-left-module-Commutative-Ring
            ( right-additive-rel-tensor-product-left-module-Commutative-Ring
              ( m)
              ( n)
              ( n'))))

    is-right-homogeneous-in-tensor-product-left-module-Commutative-Ring :
      (m : type-left-module-Commutative-Ring R M)
      (r : type-Commutative-Ring R)
      (n : type-left-module-Commutative-Ring R N) →
      in-tensor-product-left-module-Commutative-Ring
        ( m)
        ( mul-left-module-Commutative-Ring R N r n) ＝
      mul-tensor-product-left-module-Commutative-Ring
        ( r)
        ( in-tensor-product-left-module-Commutative-Ring m n)
    is-right-homogeneous-in-tensor-product-left-module-Commutative-Ring m r n =
      inv
        ( ( compute-mul-tensor-product-left-module-Commutative-Ring _ _) ∙
          ( eq-in-type-free-tensor-product-left-module-Commutative-Ring
            (right-homogeneous-rel-tensor-product-left-module-Commutative-Ring
              ( r)
              ( m)
              ( n))))

  is-bilinear-map-in-tensor-product-left-module-Commutative-Ring :
    is-bilinear-map-left-module-Commutative-Ring
      ( R)
      ( M)
      ( N)
      ( tensor-product-left-module-Commutative-Ring)
      ( in-tensor-product-left-module-Commutative-Ring)
  is-bilinear-map-in-tensor-product-left-module-Commutative-Ring =
    ( ( λ n →
        ( is-left-additive-in-tensor-product-left-module-Commutative-Ring n ,
          is-left-homogeneous-in-tensor-product-left-module-Commutative-Ring
            ( n))) ,
      ( λ m →
        ( is-right-additive-in-tensor-product-left-module-Commutative-Ring m ,
          is-right-homogeneous-in-tensor-product-left-module-Commutative-Ring
            ( m))))

  bilinear-map-tensor-product-left-module-Commutative-Ring :
    bilinear-map-left-module-Commutative-Ring
      ( R)
      ( M)
      ( N)
      ( tensor-product-left-module-Commutative-Ring)
  bilinear-map-tensor-product-left-module-Commutative-Ring =
    ( in-tensor-product-left-module-Commutative-Ring ,
      is-bilinear-map-in-tensor-product-left-module-Commutative-Ring)
```
