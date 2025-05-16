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

To do this, we introduce the type `Precategory-Expression`, which is a syntactic
representation of a morphism. Then, noting that every morphism is represented by
an expression (through `in-Precategory-Expression`), it will be sufficient to
prove an equality of expressions to prove an equality of morphisms. However, if
two morphisms are equal, then their normalized expressions are equal by
reflexivity, so that the problem is reduced to finding which
`Precategory-Expression` represents a given morphism.

This last problem, as well as the application of the
`solve-Precategory-Expression` lemma, is what the macro automates.

## Definition

### The syntactic representation of a morphism

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  where

  data
    Precategory-Expression :
      obj-Precategory C → obj-Precategory C → UU (l1 ⊔ l2)
    where
    id-hom-Precategory-Expression :
      {x : obj-Precategory C} → Precategory-Expression x x
    hom-Precategory-Expression :
      {x y : obj-Precategory C} →
      hom-Precategory C x y → Precategory-Expression x y
    comp-hom-Precategory-Expression :
      {x y z : obj-Precategory C} →
      Precategory-Expression y z →
      Precategory-Expression x y →
      Precategory-Expression x z
```

### The syntactic representation of a morphism

```agda
  in-Precategory-Expression :
    {x y : obj-Precategory C} →
    Precategory-Expression x y →
    hom-Precategory C x y
  in-Precategory-Expression id-hom-Precategory-Expression = id-hom-Precategory C
  in-Precategory-Expression (hom-Precategory-Expression f) = f
  in-Precategory-Expression (comp-hom-Precategory-Expression f g) =
    comp-hom-Precategory C
      ( in-Precategory-Expression f)
      ( in-Precategory-Expression g)
```

### The normalization of the syntactic representation of a morphism

```agda
  eval-Precategory-Expression :
    {x y z : obj-Precategory C} →
    Precategory-Expression y z →
    hom-Precategory C x y →
    hom-Precategory C x z
  eval-Precategory-Expression id-hom-Precategory-Expression f = f
  eval-Precategory-Expression (hom-Precategory-Expression f) g =
    comp-hom-Precategory C f g
  eval-Precategory-Expression (comp-hom-Precategory-Expression f g) h =
    eval-Precategory-Expression f (eval-Precategory-Expression g h)

  is-sound-eval-Precategory-Expression :
    {x y z : obj-Precategory C}
    (e : Precategory-Expression y z)
    (f : hom-Precategory C x y) →
    ( eval-Precategory-Expression e f) ＝
    ( comp-hom-Precategory C (in-Precategory-Expression e) f)
  is-sound-eval-Precategory-Expression id-hom-Precategory-Expression f =
    inv (left-unit-law-comp-hom-Precategory C f)
  is-sound-eval-Precategory-Expression (hom-Precategory-Expression f) g = refl
  is-sound-eval-Precategory-Expression (comp-hom-Precategory-Expression f g) h =
    ( is-sound-eval-Precategory-Expression
      ( f)
      ( eval-Precategory-Expression g h)) ∙
    ( ap
      ( comp-hom-Precategory C (in-Precategory-Expression f))
      ( is-sound-eval-Precategory-Expression g h)) ∙
    ( inv
      ( associative-comp-hom-Precategory
        C (in-Precategory-Expression f) (in-Precategory-Expression g) h))

  normalize-Precategory-Expression :
    {x y : obj-Precategory C} →
    Precategory-Expression x y →
    hom-Precategory C x y
  normalize-Precategory-Expression e =
    eval-Precategory-Expression e (id-hom-Precategory C)

  is-sound-normalize-Precategory-Expression :
    {x y : obj-Precategory C} →
    (e : Precategory-Expression x y) →
    normalize-Precategory-Expression e ＝ in-Precategory-Expression e
  is-sound-normalize-Precategory-Expression e =
    ( is-sound-eval-Precategory-Expression e (id-hom-Precategory C)) ∙
    ( right-unit-law-comp-hom-Precategory C (in-Precategory-Expression e))

  abstract
    solve-Precategory-Expression :
      {x y : obj-Precategory C} →
      (f g : Precategory-Expression x y) →
      normalize-Precategory-Expression f ＝ normalize-Precategory-Expression g →
      in-Precategory-Expression f ＝ in-Precategory-Expression g
    solve-Precategory-Expression f g p =
      ( inv (is-sound-normalize-Precategory-Expression f)) ∙
      ( p) ∙
      ( is-sound-normalize-Precategory-Expression g)
```

## The macro definition

### The conversion of a morphism into an expression

```agda
private
  infixr 11 _∷_
  pattern _∷_ x xs = cons x xs
  _++_ : {l : Level} {A : UU l} → list A → list A → list A
  _++_ = concat-list
  infixr 10 _++_

  pattern apply-pr1 xs =
    definition-Term-Agda (quote pr1)
      ( hidden-Argument-Agda unknown-Term-Agda ∷
        hidden-Argument-Agda unknown-Term-Agda ∷
        hidden-Argument-Agda unknown-Term-Agda ∷
        hidden-Argument-Agda unknown-Term-Agda ∷
        xs)

  pattern apply-pr2 xs =
    definition-Term-Agda (quote pr2)
      ( hidden-Argument-Agda unknown-Term-Agda ∷
        hidden-Argument-Agda unknown-Term-Agda ∷
        hidden-Argument-Agda unknown-Term-Agda ∷
        hidden-Argument-Agda unknown-Term-Agda ∷
        xs)
```

### Building a term of `Precategory-Expression C x y` from a term of type `hom-Precategory C x y`

```agda
build-Precategory-Expression : Term-Agda → Term-Agda
build-Precategory-Expression
  ( apply-pr1
    ( visible-Argument-Agda
      ( apply-pr2
        ( visible-Argument-Agda
          ( apply-pr2
            ( visible-Argument-Agda
              ( apply-pr2 (visible-Argument-Agda C ∷ nil)) ∷
              ( nil))) ∷
            ( nil))) ∷
          ( visible-Argument-Agda x) ∷
          nil)) =
  constructor-Term-Agda (quote id-hom-Precategory-Expression) nil
build-Precategory-Expression
  ( apply-pr1
    ( visible-Argument-Agda
      ( apply-pr1
        ( visible-Argument-Agda
          ( apply-pr2
            ( visible-Argument-Agda
              ( apply-pr2
                (visible-Argument-Agda C ∷ nil)) ∷ nil))
            ∷ nil)) ∷
      hidden-Argument-Agda x ∷ hidden-Argument-Agda y ∷ hidden-Argument-Agda z ∷
      visible-Argument-Agda g ∷ visible-Argument-Agda f ∷ nil)) =
  constructor-Term-Agda
    ( quote comp-hom-Precategory-Expression)
    ( visible-Argument-Agda (build-Precategory-Expression g) ∷
      visible-Argument-Agda (build-Precategory-Expression f) ∷
      nil)
build-Precategory-Expression f =
  constructor-Term-Agda
    ( quote hom-Precategory-Expression)
    ( visible-Argument-Agda f ∷ nil)
```

### The application of the `solve-Precategory-Expression` lemma

```agda
apply-solve-Precategory-Expression :
  Term-Agda → Term-Agda → Term-Agda → Term-Agda
apply-solve-Precategory-Expression cat lhs rhs =
  definition-Term-Agda
    ( quote solve-Precategory-Expression)
    ( replicate-hidden-Argument-Agda 2 ++
      visible-Argument-Agda cat ∷
      replicate-hidden-Argument-Agda 2 ++
      visible-Argument-Agda lhs ∷
      visible-Argument-Agda rhs ∷
      visible-Argument-Agda (constructor-Term-Agda (quote refl) nil) ∷
      nil)
```

### The macro definition

```agda
macro
  solve-Precategory! : Term-Agda → Term-Agda → type-Type-Checker unit
  solve-Precategory! cat hole = do
    goal ← infer-type hole >>= reduce
    (lhs , rhs) ← boundary-Type-Checker goal
    built-lhs ←
      normalize lhs >>= (return-Type-Checker ∘ build-Precategory-Expression)
    built-rhs ←
      normalize rhs >>= (return-Type-Checker ∘ build-Precategory-Expression)
    unify hole (apply-solve-Precategory-Expression cat built-lhs built-rhs)
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
      {f : hom-Precategory C x y} →
      f ＝ f
    _ = solve-Precategory! C

    _ :
      {x : obj-Precategory C} →
      id-hom-Precategory C {x} ＝ id-hom-Precategory C {x}
    _ = solve-Precategory! C

    _ :
      {a b c : obj-Precategory C}
      {f : hom-Precategory C a b}
      {g : hom-Precategory C b c} →
      (comp-hom-Precategory C g f) ＝
      comp-hom-Precategory C g f
    _ = solve-Precategory! C

    _ :
      {a b c d : obj-Precategory C}
      {f : hom-Precategory C a b}
      {g : hom-Precategory C b c} →
      {h : hom-Precategory C c d} →
      comp-hom-Precategory C h (comp-hom-Precategory C g f) ＝
      comp-hom-Precategory C (comp-hom-Precategory C h g) f
    _ = solve-Precategory! C

    _ :
      {a b c d : obj-Precategory C}
      {f : hom-Precategory C a b}
      {g : hom-Precategory C b c} →
      {h : hom-Precategory C c d} →
      comp-hom-Precategory C
        ( comp-hom-Precategory C h (id-hom-Precategory C))
        ( comp-hom-Precategory C g f) ＝
      comp-hom-Precategory C
        ( comp-hom-Precategory C h g)
        ( comp-hom-Precategory C (id-hom-Precategory C) f)
    _ = solve-Precategory! C
```
