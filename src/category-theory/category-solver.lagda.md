# A category solver

```agda
module category-theory.category-solver where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.functions
open import foundation.identity-types
open import foundation.cartesian-product-types
open import reflection.arguments
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.equational-reasoning
open import lists.lists
open import lists.concatenation-lists
open import reflection.terms
open import reflection.type-checking-monad
```

</details>

## Idea

A pregroupoid is a precategory in which every morphism is an isomorphism.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precat l1 l2)
  where

  data Precat-Expr : obj-Precat C → obj-Precat C → UU (l1 ⊔ l2) where
    id-hom-Precat-Expr : {x : obj-Precat C} → Precat-Expr x x
    type-hom-Precat-Expr :
      {x y : obj-Precat C} → type-hom-Precat C x y → Precat-Expr x y
    comp-hom-Precat-Expr :
      {x y z : obj-Precat C} → Precat-Expr y z → Precat-Expr x y → Precat-Expr x z

  in-Precat-Expr :
    {x y : obj-Precat C} →
    Precat-Expr x y →
    type-hom-Precat C x y
  in-Precat-Expr id-hom-Precat-Expr = id-hom-Precat C
  in-Precat-Expr (type-hom-Precat-Expr f) = f
  in-Precat-Expr (comp-hom-Precat-Expr f g) =
    comp-hom-Precat C (in-Precat-Expr f) (in-Precat-Expr g)

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
        by ap (comp-hom-Precat C (in-Precat-Expr f)) (is-sound-eval-Precat-Expr g h)
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

  -------------------------------------
  private
    infixr 10 _∷_
    pattern _∷_ x xs = cons x xs
    _++_ : {l : Level} {A : UU l} → list A → list A → list A
    _++_ = concat-list
    infixr 5 _++_

  mk-category-args : Term → list (Arg Term) → list (Arg Term)
  mk-category-args cat xs =
    hidden-Arg unknown ∷
    hidden-Arg unknown ∷
    hidden-Arg cat ∷
    xs

  “solve” : Term → Term → Term → Term
  “solve” cat lhs rhs =
    def
      ( quote solve-Precat-Expr)
      ( mk-category-args
        ( cat)
        ( replicate-hidden-Arg 2 ++
          ( visible-Arg lhs ∷
            visible-Arg rhs ∷
            visible-Arg (def (quote refl) nil) ∷
            nil)))

  -- “nf” : Term → Term → Term
  -- “nf” cat e =
  --   def
  --     ( quote normalize-Precat-Expr)
  --     ( mk-category-args
  --       ( cat)
  --       ( infer-hidden 2 (visible-Arg e ∷ nil)))

  test :
    {x y z : obj-Precat C}
    {f : type-hom-Precat C x y}
    {g : type-hom-Precat C y z} →
    quoteTerm (comp-hom-Precat C g f) ＝
      def (quote comp-hom-Precat)
       (hidden-Arg (var 9 nil) ∷
        hidden-Arg (var 8 nil) ∷
        visible-Arg (var 5 nil) ∷
        hidden-Arg (var 4 nil) ∷
        hidden-Arg (var 3 nil) ∷
        hidden-Arg (var 2 nil) ∷
        visible-Arg (var 0 nil) ∷
        visible-Arg (var 1 nil) ∷
        nil)
  test = refl

  test' :
    quoteTerm (id-hom-Precat C) ＝
      def (quote id-hom-Precat)
       (hidden-Arg (var 4 nil) ∷
        hidden-Arg (var 3 nil) ∷
        visible-Arg (var 0 nil) ∷
        nil)
  test' = refl

  test'' :
    {x y : obj-Precat C}
    {f : type-hom-Precat C x y} →
    quoteTerm (type-hom-Precat-Expr f) ＝
      con (quote type-hom-Precat-Expr)
      (arg (arg-info hidden (modality relevant quantity-ω)) (var 2 nil) ∷
       arg (arg-info hidden (modality relevant quantity-ω)) (var 1 nil) ∷
       arg (arg-info visible (modality relevant quantity-ω)) (var 0 nil) ∷
       nil)
  test'' = refl

  tesat'' :
    {x y : obj-Precat C}
    {f : type-hom-Precat C x y} →
    quoteTerm f ＝
      var 0 nil
  tesat'' = refl


  -- Builds a term of `Precat-Expr C x y` from a term of type `type-hom-Precat C x y`
  build-Precat-Expr : Term → Term
  build-Precat-Expr f =
    con (quote type-hom-Precat-Expr) (visible-Arg f ∷ nil)

  -- san' :
  --   {x y : obj-Precat C}
  --   {f : type-hom-Precat C x y} →
  --   build-Precat-Expr (quoteTerm f) ＝
  --   quoteTerm (type-hom-Precat-Expr f)
  -- san' = refl --refl

  -- san :
  --   {x y z : obj-Precat C}
  --   {f : type-hom-Precat C x y}
  --   {g : type-hom-Precat C y z} →
  --   build-Precat-Expr (quoteTerm (comp-hom-Precat C g f)) ＝ (quoteTerm (comp-hom-Precat-Expr g f))
  -- san = _


  -- build-expr : Term → Term
  -- build-expr def (quote Precategory.id) (category-args (hidden-Arg ∷ )) = con (quote NbE.`id) []
  -- build-expr (“∘” f g) = con (quote NbE._`∘_) (build-expr f v∷ build-expr g v∷ [] )
  -- build-expr f = con (quote NbE._↑) (f v∷ [])

  macro
    solve-Precat! : Term → Term → TC unit
    solve-Precat! cat hole = do
      goal <- inferType hole -- >>= normalise
      (l , r) <- boundary-TCM hole
      elhs ← normalise l >>= (returnTC ∘ build-Precat-Expr)
      erhs ← normalise r >>= (returnTC ∘ build-Precat-Expr)
      unify hole (“solve” cat l r)

  private
    test1 :
      {x y : obj-Precat C}
      {f : type-hom-Precat C x y} →
      -- f ＝ f
      quoteTerm (f ＝ f) ＝
       def (quote _＝_)
        (arg (arg-info hidden (modality relevant quantity-ω)) (var 6 nil) ∷
        --type
         arg (arg-info hidden (modality relevant quantity-ω))
         (def (quote pr1)
          (arg (arg-info hidden (modality relevant quantity-ω)) unknown ∷
           arg (arg-info hidden (modality relevant quantity-ω)) unknown ∷
           arg (arg-info hidden (modality relevant quantity-ω)) unknown ∷
           arg (arg-info hidden (modality relevant quantity-ω)) unknown ∷
           arg (arg-info visible (modality relevant quantity-ω))
           (def (quote pr1)
            (arg (arg-info hidden (modality relevant quantity-ω)) unknown ∷
             arg (arg-info hidden (modality relevant quantity-ω)) unknown ∷
             arg (arg-info hidden (modality relevant quantity-ω)) unknown ∷
             arg (arg-info hidden (modality relevant quantity-ω)) unknown ∷
             arg (arg-info visible (modality relevant quantity-ω))
             (def (quote pr2)
              (arg (arg-info hidden (modality relevant quantity-ω)) unknown ∷
               arg (arg-info hidden (modality relevant quantity-ω)) unknown ∷
               arg (arg-info hidden (modality relevant quantity-ω)) unknown ∷
               arg (arg-info hidden (modality relevant quantity-ω)) unknown ∷
               arg (arg-info visible (modality relevant quantity-ω)) (var 3 nil) ∷
               nil))
             ∷
             arg (arg-info visible (modality relevant quantity-ω)) (var 2 nil) ∷
             arg (arg-info visible (modality relevant quantity-ω)) (var 1 nil) ∷
             nil))
           ∷ nil))
         ∷
         -- lhs
         arg (arg-info visible (modality relevant quantity-ω)) (var 0 nil) ∷
         -- rhs
         arg (arg-info visible (modality relevant quantity-ω)) (var 0 nil) ∷
         nil)
    test1 = refl -- solve-Precat! C

    hurr :
      {x y : obj-Precat C}
      (f : type-hom-Precat C x y) →
      TC (Term × Term)
    hurr f = boundary-TCM (quoteTerm (f))

    test1' :
      {x y : obj-Precat C}
      {f : type-hom-Precat C x y} →
      f ＝ f
    test1' = solve-Precat! C
```
