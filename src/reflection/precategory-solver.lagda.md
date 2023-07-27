# Precategory solver

```agda
{-# OPTIONS --no-exact-split #-}

module reflection.precategory-solver where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import lists.concatenation-lists
open import lists.lists

open import reflection.arguments
open import reflection.terms
open import reflection.type-checking-monad
```

</details>

## Idea

This module defines a macro, `solve-Precategory!` that solves any equation
between morphisms of a precategory, as long as it's derivable from the axioms of
precategories.

To do this, we introduce the type `Precategory-Expr`, which is a syntactic
representation of a morphism. Then, noting that every morphism is represented by
an expression (through `in-Precategory-Expr`), it will be sufficient to prove an
equality of expresions to prove an equality of morphisms. However, if two
morphisms are equal, then their normalized expressions are equal by reflexivity,
so that the problem is reduced to finding which `Precategory-Expr` represents a
given morphism.

This last problem, as well as the application of the `solve-Precategory-Expr`
lemma, is what the macro automates.

## Definition

### The syntactic representation of a morphism

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  where

  data
    Precategory-Expr :
      obj-Precategory C → obj-Precategory C → UU (l1 ⊔ l2)
    where
    id-hom-Precategory-Expr :
      {x : obj-Precategory C} → Precategory-Expr x x
    type-hom-Precategory-Expr :
      {x y : obj-Precategory C} →
      type-hom-Precategory C x y → Precategory-Expr x y
    comp-hom-Precategory-Expr :
      {x y z : obj-Precategory C} →
      Precategory-Expr y z → Precategory-Expr x y → Precategory-Expr x z
```

### The syntactic representation of a morphism

```agda
  in-Precategory-Expr :
    {x y : obj-Precategory C} →
    Precategory-Expr x y →
    type-hom-Precategory C x y
  in-Precategory-Expr id-hom-Precategory-Expr = id-hom-Precategory C
  in-Precategory-Expr (type-hom-Precategory-Expr f) = f
  in-Precategory-Expr (comp-hom-Precategory-Expr f g) =
    comp-hom-Precategory C (in-Precategory-Expr f) (in-Precategory-Expr g)
```

### The normalization of the syntactic representation of a morphism

```agda
  eval-Precategory-Expr :
    {x y z : obj-Precategory C} →
    Precategory-Expr y z →
    type-hom-Precategory C x y →
    type-hom-Precategory C x z
  eval-Precategory-Expr id-hom-Precategory-Expr f = f
  eval-Precategory-Expr (type-hom-Precategory-Expr f) g =
    comp-hom-Precategory C f g
  eval-Precategory-Expr (comp-hom-Precategory-Expr f g) h =
    eval-Precategory-Expr f (eval-Precategory-Expr g h)

  is-sound-eval-Precategory-Expr :
    {x y z : obj-Precategory C}
    (e : Precategory-Expr y z)
    (f : type-hom-Precategory C x y) →
    ( eval-Precategory-Expr e f) ＝
    ( comp-hom-Precategory C (in-Precategory-Expr e) f)
  is-sound-eval-Precategory-Expr id-hom-Precategory-Expr f =
    inv (left-unit-law-comp-hom-Precategory C f)
  is-sound-eval-Precategory-Expr (type-hom-Precategory-Expr f) g = refl
  is-sound-eval-Precategory-Expr (comp-hom-Precategory-Expr f g) h =
    equational-reasoning
    eval-Precategory-Expr f (eval-Precategory-Expr g h)
      ＝ comp-hom-Precategory C
          ( in-Precategory-Expr f)
          ( eval-Precategory-Expr g h)
        by is-sound-eval-Precategory-Expr f (eval-Precategory-Expr g h)
      ＝ comp-hom-Precategory C
          ( in-Precategory-Expr f)
          ( comp-hom-Precategory C (in-Precategory-Expr g) h)
        by ap
          ( comp-hom-Precategory C (in-Precategory-Expr f))
          ( is-sound-eval-Precategory-Expr g h)
      ＝ comp-hom-Precategory C
          ( comp-hom-Precategory C
            ( in-Precategory-Expr f)
            ( in-Precategory-Expr g))
          h
        by
          inv
            ( associative-comp-hom-Precategory
              C (in-Precategory-Expr f) (in-Precategory-Expr g) h)

  normalize-Precategory-Expr :
    {x y : obj-Precategory C} →
    Precategory-Expr x y →
    type-hom-Precategory C x y
  normalize-Precategory-Expr e = eval-Precategory-Expr e (id-hom-Precategory C)

  is-sound-normalize-Precategory-Expr :
    {x y : obj-Precategory C} →
    (e : Precategory-Expr x y) →
    normalize-Precategory-Expr e ＝ in-Precategory-Expr e
  is-sound-normalize-Precategory-Expr e = equational-reasoning
    eval-Precategory-Expr e (id-hom-Precategory C)
      ＝ comp-hom-Precategory C (in-Precategory-Expr e) (id-hom-Precategory C)
        by is-sound-eval-Precategory-Expr e (id-hom-Precategory C)
      ＝ in-Precategory-Expr e
        by right-unit-law-comp-hom-Precategory C (in-Precategory-Expr e)

  abstract
    solve-Precategory-Expr :
      {x y : obj-Precategory C} →
      (f g : Precategory-Expr x y) →
      normalize-Precategory-Expr f ＝ normalize-Precategory-Expr g →
      in-Precategory-Expr f ＝ in-Precategory-Expr g
    solve-Precategory-Expr f g p = equational-reasoning
      in-Precategory-Expr f
      ＝ normalize-Precategory-Expr f
        by inv (is-sound-normalize-Precategory-Expr f)
      ＝ normalize-Precategory-Expr g
        by p
      ＝ in-Precategory-Expr g
        by is-sound-normalize-Precategory-Expr g
```

## The macro definition

### The conversion of a morphism into an expression

```agda
private
  infixr 10 _∷_
  pattern _∷_ x xs = cons x xs
  _++_ : {l : Level} {A : UU l} → list A → list A → list A
  _++_ = concat-list
  infixr 5 _++_

  pattern apply-pr1 xs =
    def (quote pr1)
      ( hidden-Arg unknown ∷
        hidden-Arg unknown ∷
        hidden-Arg unknown ∷
        hidden-Arg unknown ∷
        xs)

  pattern apply-pr2 xs =
    def (quote pr2)
      ( hidden-Arg unknown ∷
        hidden-Arg unknown ∷
        hidden-Arg unknown ∷
        hidden-Arg unknown ∷
        xs)
```

### Building a term of `Precategory-Expr C x y` from a term of type `type-hom-Precategory C x y`

```agda
build-Precategory-Expr : Term → Term
build-Precategory-Expr
  ( apply-pr1
    ( visible-Arg
      ( apply-pr2
        ( visible-Arg
          ( apply-pr2
            ( visible-Arg
              ( apply-pr2 (visible-Arg C ∷ nil)) ∷
              ( nil))) ∷
            ( nil))) ∷
          ( visible-Arg x) ∷
          nil)) =
  con (quote id-hom-Precategory-Expr) nil
build-Precategory-Expr
  ( apply-pr1
    ( visible-Arg
      ( apply-pr1
        ( visible-Arg
          ( apply-pr2
            ( visible-Arg
              ( apply-pr2
                (visible-Arg C ∷ nil)) ∷ nil))
            ∷ nil)) ∷
      hidden-Arg x ∷ hidden-Arg y ∷ hidden-Arg z ∷
      visible-Arg g ∷ visible-Arg f ∷ nil)) =
  con
    ( quote comp-hom-Precategory-Expr)
    ( visible-Arg (build-Precategory-Expr g) ∷
      visible-Arg (build-Precategory-Expr f) ∷
      nil)
build-Precategory-Expr f =
  con (quote type-hom-Precategory-Expr) (visible-Arg f ∷ nil)
```

### The application of the `solve-Precategory-Expr` lemma

```agda
apply-solve-Precategory-Expr : Term → Term → Term → Term
apply-solve-Precategory-Expr cat lhs rhs =
  def
    ( quote solve-Precategory-Expr)
    ( replicate-hidden-Arg 2 ++
      visible-Arg cat ∷
      replicate-hidden-Arg 2 ++
      visible-Arg lhs ∷
      visible-Arg rhs ∷
      visible-Arg (con (quote refl) nil) ∷
      nil)
```

### The macro definition

```agda
macro
  solve-Precategory! : Term → Term → TC unit
  solve-Precategory! cat hole = do
    goal ← inferType hole >>= reduce
    (lhs , rhs) ← boundary-TCM goal
    built-lhs ← normalise lhs >>= (returnTC ∘ build-Precategory-Expr)
    built-rhs ← normalise rhs >>= (returnTC ∘ build-Precategory-Expr)
    unify hole (apply-solve-Precategory-Expr cat built-lhs built-rhs)
```

## Examples

```agda
module _
  {l1 l2 : Level}
  {C : Precategory l1 l2}
  where

  private
    _ :
      {x y : obj-Precategory C}
      {f : type-hom-Precategory C x y} →
      f ＝ f
    _ = solve-Precategory! C

    _ :
      {x : obj-Precategory C} →
      id-hom-Precategory C {x} ＝ id-hom-Precategory C {x}
    _ = solve-Precategory! C

    _ :
      {a b c : obj-Precategory C}
      {f : type-hom-Precategory C a b}
      {g : type-hom-Precategory C b c} →
      (comp-hom-Precategory C g f) ＝
      comp-hom-Precategory C g f
    _ = solve-Precategory! C

    _ :
      {a b c d : obj-Precategory C}
      {f : type-hom-Precategory C a b}
      {g : type-hom-Precategory C b c} →
      {h : type-hom-Precategory C c d} →
      comp-hom-Precategory C h (comp-hom-Precategory C g f) ＝
      comp-hom-Precategory C (comp-hom-Precategory C h g) f
    _ = solve-Precategory! C

    _ :
      {a b c d : obj-Precategory C}
      {f : type-hom-Precategory C a b}
      {g : type-hom-Precategory C b c} →
      {h : type-hom-Precategory C c d} →
      comp-hom-Precategory C
        ( comp-hom-Precategory C h (id-hom-Precategory C))
        ( comp-hom-Precategory C g f) ＝
      comp-hom-Precategory C
        ( comp-hom-Precategory C h g)
        ( comp-hom-Precategory C (id-hom-Precategory C) f)
    _ = solve-Precategory! C
```
