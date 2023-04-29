# A precategory solver

```agda
{-# OPTIONS --no-exact-split  #-}
module category-theory.precategory-solver where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.equational-reasoning
open import foundation.functions
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

This module defines a macro, `solve-Precat!` that solves any equation between
morphisms of a precategory, as long as it's derivable from the axioms of
precategories.

To do this, we introduce the type `Precat-Expr`, which is a syntactic
representation of a morphism. Then, noting that every morphism is represented by
an expression (through `in-Precat-Expr`), it will be sufficient to prove an
equality of expresions to prove an equality of morphisms. However, if two
morphisms are equal, then their normalized expressions are equal by reflexivity,
so that the problem is reduced to finding which `Precat-Expr` represents a given
morphism.

This last problem, as well as the application of the `solve-Precat-Expr` lemma,
is what the macro automates.

## Definition

### The syntactic representation of a morphism

```agda
module _
  {l1 l2 : Level}
  (C : Precat l1 l2)
  where

  data Precat-Expr : obj-Precat C → obj-Precat C → UU (l1 ⊔ l2) where
    id-hom-Precat-Expr : {x : obj-Precat C} → Precat-Expr x x
    type-hom-Precat-Expr :
      {x y : obj-Precat C} → type-hom-Precat C x y → Precat-Expr x y
    comp-hom-Precat-Expr :
      {x y z : obj-Precat C} →
      Precat-Expr y z → Precat-Expr x y → Precat-Expr x z
```

### The syntactic representation of a morphism

```agda
  in-Precat-Expr :
    {x y : obj-Precat C} →
    Precat-Expr x y →
    type-hom-Precat C x y
  in-Precat-Expr id-hom-Precat-Expr = id-hom-Precat C
  in-Precat-Expr (type-hom-Precat-Expr f) = f
  in-Precat-Expr (comp-hom-Precat-Expr f g) =
    comp-hom-Precat C (in-Precat-Expr f) (in-Precat-Expr g)
```

### The normalization of the syntactic representation of a morphism

```agda
  eval-Precat-Expr :
    {x y z : obj-Precat C} →
    Precat-Expr y z →
    type-hom-Precat C x y →
    type-hom-Precat C x z
  eval-Precat-Expr id-hom-Precat-Expr f = f
  eval-Precat-Expr (type-hom-Precat-Expr f) g = comp-hom-Precat C f g
  eval-Precat-Expr (comp-hom-Precat-Expr f g) h =
    eval-Precat-Expr f (eval-Precat-Expr g h)

  is-sound-eval-Precat-Expr :
    {x y z : obj-Precat C}
    (e : Precat-Expr y z)
    (f : type-hom-Precat C x y) →
    (eval-Precat-Expr e f) ＝ (comp-hom-Precat C (in-Precat-Expr e) f)
  is-sound-eval-Precat-Expr id-hom-Precat-Expr f =
    inv (left-unit-law-comp-hom-Precat C f)
  is-sound-eval-Precat-Expr (type-hom-Precat-Expr f) g = refl
  is-sound-eval-Precat-Expr (comp-hom-Precat-Expr f g) h = equational-reasoning
    eval-Precat-Expr f (eval-Precat-Expr g h)
      ＝ comp-hom-Precat C (in-Precat-Expr f) (eval-Precat-Expr g h)
        by is-sound-eval-Precat-Expr f (eval-Precat-Expr g h)
      ＝ comp-hom-Precat C
          (in-Precat-Expr f)
          (comp-hom-Precat C (in-Precat-Expr g) h)
        by ap
          ( comp-hom-Precat C (in-Precat-Expr f))
          ( is-sound-eval-Precat-Expr g h)
      ＝ comp-hom-Precat C
          (comp-hom-Precat C (in-Precat-Expr f) (in-Precat-Expr g))
          h
        by inv (assoc-comp-hom-Precat C (in-Precat-Expr f) (in-Precat-Expr g) h)

  normalize-Precat-Expr :
    {x y : obj-Precat C} →
    Precat-Expr x y →
    type-hom-Precat C x y
  normalize-Precat-Expr e = eval-Precat-Expr e (id-hom-Precat C)

  is-sound-normalize-Precat-Expr :
    {x y : obj-Precat C} →
    (e : Precat-Expr x y) →
    normalize-Precat-Expr e ＝ in-Precat-Expr e
  is-sound-normalize-Precat-Expr e = equational-reasoning
    eval-Precat-Expr e (id-hom-Precat C)
      ＝ comp-hom-Precat C (in-Precat-Expr e) (id-hom-Precat C)
        by is-sound-eval-Precat-Expr e (id-hom-Precat C)
      ＝ in-Precat-Expr e
        by right-unit-law-comp-hom-Precat C (in-Precat-Expr e)

  abstract
    solve-Precat-Expr :
      {x y : obj-Precat C} →
      (f g : Precat-Expr x y) →
      normalize-Precat-Expr f ＝ normalize-Precat-Expr g →
      in-Precat-Expr f ＝ in-Precat-Expr g
    solve-Precat-Expr f g p = equational-reasoning
      in-Precat-Expr f
      ＝ normalize-Precat-Expr f
        by inv (is-sound-normalize-Precat-Expr f)
      ＝ normalize-Precat-Expr g
        by p
      ＝ in-Precat-Expr g
        by is-sound-normalize-Precat-Expr g
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

-- Builds a term of `Precat-Expr C x y` from a term of type `type-hom-Precat C x y`
build-Precat-Expr : Term → Term
build-Precat-Expr
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
  con (quote id-hom-Precat-Expr) nil
build-Precat-Expr
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
    ( quote comp-hom-Precat-Expr)
    ( visible-Arg (build-Precat-Expr g) ∷
      visible-Arg (build-Precat-Expr f) ∷
      nil)
build-Precat-Expr f =
  con (quote type-hom-Precat-Expr) (visible-Arg f ∷ nil)
```

### The application of the `solve-Precat-Expr` lemma

```agda
apply-solve-Precat-Expr : Term → Term → Term → Term
apply-solve-Precat-Expr cat lhs rhs =
  def
    ( quote solve-Precat-Expr)
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
  solve-Precat! : Term → Term → TC unit
  solve-Precat! cat hole = do
    goal ← inferType hole >>= reduce
    (lhs , rhs) ← boundary-TCM goal
    built-lhs ← normalise lhs >>= (returnTC ∘ build-Precat-Expr)
    built-rhs ← normalise rhs >>= (returnTC ∘ build-Precat-Expr)
    unify hole (apply-solve-Precat-Expr cat built-lhs built-rhs)
```

## Examples

```agda
module _
  {l1 l2 : Level}
  {C : Precat l1 l2}
  where

  private
    _ :
      {x y : obj-Precat C}
      {f : type-hom-Precat C x y} →
      f ＝ f
    _ = solve-Precat! C

    _ :
      {x : obj-Precat C} →
      id-hom-Precat C {x} ＝ id-hom-Precat C {x}
    _ = solve-Precat! C

    _ :
      {a b c : obj-Precat C}
      {f : type-hom-Precat C a b}
      {g : type-hom-Precat C b c} →
      (comp-hom-Precat C g f) ＝
      comp-hom-Precat C g f
    _ = solve-Precat! C

    _ :
      {a b c d : obj-Precat C}
      {f : type-hom-Precat C a b}
      {g : type-hom-Precat C b c} →
      {h : type-hom-Precat C c d} →
      comp-hom-Precat C h (comp-hom-Precat C g f) ＝
      comp-hom-Precat C (comp-hom-Precat C h g) f
    _ = solve-Precat! C

    _ :
      {a b c d : obj-Precat C}
      {f : type-hom-Precat C a b}
      {g : type-hom-Precat C b c} →
      {h : type-hom-Precat C c d} →
      comp-hom-Precat C
        ( comp-hom-Precat C h (id-hom-Precat C))
        ( comp-hom-Precat C g f) ＝
      comp-hom-Precat C
        ( comp-hom-Precat C h g)
        ( comp-hom-Precat C (id-hom-Precat C) f)
    _ = solve-Precat! C
```
