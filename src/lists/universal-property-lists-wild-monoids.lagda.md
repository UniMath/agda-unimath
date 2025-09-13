# The universal property of lists with respect to wild monoids

```agda
module lists.universal-property-lists-wild-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-higher-homotopies-composition

open import group-theory.homomorphisms-semigroups

open import lists.concatenation-lists
open import lists.lists

open import structured-types.h-spaces
open import structured-types.morphisms-h-spaces
open import structured-types.morphisms-wild-monoids
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.wild-monoids
```

</details>

## Idea

The type of lists of elements of `X` is the initial wild monoid equipped with a
map from `X` into it.

## Definition

### The pointed type of lists of elements of `X`

```agda
list-pointed-type : {l : Level} → UU l → Pointed-Type l
pr1 (list-pointed-type X) = list X
pr2 (list-pointed-type X) = nil
```

### The H-space of lists of elements of `X`

```agda
list-H-Space :
  {l : Level} (X : UU l) → H-Space l
pr1 (list-H-Space X) = list-pointed-type X
pr1 (pr2 (list-H-Space X)) = concat-list
pr1 (pr2 (pr2 (list-H-Space X))) = left-unit-law-concat-list
pr1 (pr2 (pr2 (pr2 (list-H-Space X)))) = right-unit-law-concat-list
pr2 (pr2 (pr2 (pr2 (list-H-Space X)))) = refl
```

### The wild monoid of lists of elements of `X`

```agda
unit-law-011-associative-concat-list :
  {l1 : Level} {X : UU l1} (y z : list X) →
  ( associative-concat-list nil y z) ∙
  ( left-unit-law-concat-list (concat-list y z)) ＝
  ( ap (λ t → concat-list t z) (left-unit-law-concat-list y))
unit-law-011-associative-concat-list y z = refl

concat-list' : {l : Level} {A : UU l} → list A → list A → list A
concat-list' x y = concat-list y x

unit-law-101-associative-concat-list :
  {l1 : Level} {X : UU l1} (x z : list X) →
  ( associative-concat-list x nil z) ∙
  ( ap (concat-list x) (left-unit-law-concat-list z)) ＝
  ( ap (λ t → concat-list t z) (right-unit-law-concat-list x))
unit-law-101-associative-concat-list nil z = refl
unit-law-101-associative-concat-list (cons x l) z =
  ( ( ( inv
        ( ap-concat
          ( cons x)
          ( associative-concat-list l nil z)
          ( ap (concat-list l) (left-unit-law-concat-list z)))) ∙
      ( left-whisker-comp²
        ( cons x)
        ( unit-law-101-associative-concat-list l)
        ( z))) ∙
    ( inv
      ( ap-comp (cons x) (concat-list' z) (right-unit-law-concat-list l)))) ∙
  ( ap-comp (concat-list' z) (cons x) (right-unit-law-concat-list l))

unit-law-110-associative-concat-list :
  {l1 : Level} {X : UU l1} (x y : list X) →
  ( associative-concat-list x y nil) ∙
  ( ap (concat-list x) (right-unit-law-concat-list y)) ＝
  ( right-unit-law-concat-list (concat-list x y))
unit-law-110-associative-concat-list nil y =
  ap-id (right-unit-law-concat-list y)
unit-law-110-associative-concat-list (cons a x) y =
  ( ap
    ( concat
      ( associative-concat-list (cons a x) y nil)
      ( concat-list (cons a x) y))
    ( ap-comp (cons a) (concat-list x) (right-unit-law-concat-list y))) ∙
  ( ( inv
      ( ap-concat
        ( cons a)
        ( associative-concat-list x y nil)
        ( ap (concat-list x) (right-unit-law-concat-list y)))) ∙
    ( left-whisker-comp²
      ( cons a)
      ( unit-law-110-associative-concat-list x)
      ( y)))

list-Wild-Monoid : {l : Level} → UU l → Wild-Monoid l
list-Wild-Monoid X =
  pair
    ( list-H-Space X)
    ( pair
      ( associative-concat-list)
      ( pair
        ( unit-law-011-associative-concat-list)
        ( pair
          ( unit-law-101-associative-concat-list)
          ( pair unit-law-110-associative-concat-list star))))
```

## Properties

### For any wild monoid `M` with a map `X → M` there is a morphism of wild monoids `list X → M`

```agda
module _
  {l1 l2 : Level} {X : UU l1} (M : Wild-Monoid l2) (f : X → type-Wild-Monoid M)
  where

  map-elim-list-Wild-Monoid :
    list X → type-Wild-Monoid M
  map-elim-list-Wild-Monoid nil = unit-Wild-Monoid M
  map-elim-list-Wild-Monoid (cons u x) =
    mul-Wild-Monoid M (f u) (map-elim-list-Wild-Monoid x)

  preserves-unit-map-elim-list-Wild-Monoid :
    map-elim-list-Wild-Monoid nil ＝ unit-Wild-Monoid M
  preserves-unit-map-elim-list-Wild-Monoid = refl

  pointed-map-elim-list-Wild-Monoid :
    list-pointed-type X →∗ pointed-type-Wild-Monoid M
  pr1 pointed-map-elim-list-Wild-Monoid =
    map-elim-list-Wild-Monoid
  pr2 pointed-map-elim-list-Wild-Monoid =
    preserves-unit-map-elim-list-Wild-Monoid

  preserves-mul-map-elim-list-Wild-Monoid :
    preserves-mul'
      ( concat-list)
      ( mul-Wild-Monoid M)
      ( map-elim-list-Wild-Monoid)
  preserves-mul-map-elim-list-Wild-Monoid nil y =
    inv (left-unit-law-mul-Wild-Monoid M (map-elim-list-Wild-Monoid y))
  preserves-mul-map-elim-list-Wild-Monoid (cons u x) y =
    ( ap (mul-Wild-Monoid M (f u))
      ( preserves-mul-map-elim-list-Wild-Monoid x y)) ∙
    ( inv
      ( associative-mul-Wild-Monoid M
        ( f u)
        ( map-elim-list-Wild-Monoid x)
        ( map-elim-list-Wild-Monoid y)))

  preserves-left-unit-law-map-elim-list-Wild-Monoid :
    preserves-left-unit-law-mul-pointed-map-H-Space
      ( list-H-Space X)
      ( h-space-Wild-Monoid M)
      ( pointed-map-elim-list-Wild-Monoid)
      ( λ {x} {y} → preserves-mul-map-elim-list-Wild-Monoid x y)
  preserves-left-unit-law-map-elim-list-Wild-Monoid x =
    inv
      ( left-inv
        ( left-unit-law-mul-Wild-Monoid M (map-elim-list-Wild-Monoid x)))

  preserves-right-unit-law-map-elim-list-Wild-Monoid :
    preserves-right-unit-law-mul-pointed-map-H-Space
      ( list-H-Space X)
      ( h-space-Wild-Monoid M)
      ( pointed-map-elim-list-Wild-Monoid)
      ( λ {x} {y} → preserves-mul-map-elim-list-Wild-Monoid x y)
  preserves-right-unit-law-map-elim-list-Wild-Monoid nil =
    ( inv (left-inv (left-unit-law-mul-Wild-Monoid M (unit-Wild-Monoid M)))) ∙
    ( ap
      ( concat
        ( inv (left-unit-law-mul-Wild-Monoid M (unit-Wild-Monoid M)))
        ( unit-Wild-Monoid M))
      ( coh-unit-laws-mul-Wild-Monoid M))
  preserves-right-unit-law-map-elim-list-Wild-Monoid (cons a x) =
    ( inv
      ( ap-comp
        ( map-elim-list-Wild-Monoid)
        ( cons a)
        ( right-unit-law-concat-list x))) ∙
    ( ( ap-comp
        ( mul-Wild-Monoid M (f a))
        ( map-elim-list-Wild-Monoid)
        ( right-unit-law-concat-list x)) ∙
      ( ( ap
          ( ap (mul-Wild-Monoid M (f a)))
          ( preserves-right-unit-law-map-elim-list-Wild-Monoid x)) ∙
        ( ( ap-concat
            ( mul-Wild-Monoid M (f a))
            ( preserves-mul-map-elim-list-Wild-Monoid x nil)
            ( right-unit-law-mul-Wild-Monoid M
              ( map-elim-list-Wild-Monoid x))) ∙
          ( ( ap
              ( concat
                ( ap
                  ( mul-Wild-Monoid M (f a))
                  ( preserves-mul-map-elim-list-Wild-Monoid x nil))
                ( map-elim-list-Wild-Monoid (cons a x)))
              ( ( ap
                  ( concat'
                    ( mul-Wild-Monoid M
                      ( f a)
                      ( mul-Wild-Monoid M
                        ( map-elim-list-Wild-Monoid x)
                        ( unit-Wild-Monoid M)))
                    ( ap
                      ( mul-Wild-Monoid M (f a))
                      ( right-unit-law-mul-Wild-Monoid M
                        ( map-elim-list-Wild-Monoid x))))
                  ( inv
                    ( left-inv
                      ( associative-mul-Wild-Monoid M
                        ( f a)
                        ( map-elim-list-Wild-Monoid x)
                        ( unit-Wild-Monoid M))))) ∙
                ( ( assoc
                    ( inv
                      ( associative-mul-Wild-Monoid M
                        ( f a)
                        ( map-elim-list-Wild-Monoid x)
                        ( unit-Wild-Monoid M)))
                    ( associative-mul-Wild-Monoid M
                      ( f a)
                      ( map-elim-list-Wild-Monoid x)
                      ( unit-Wild-Monoid M))
                    ( ap
                      ( mul-Wild-Monoid M (f a))
                      ( right-unit-law-mul-Wild-Monoid M
                        ( map-elim-list-Wild-Monoid x)))) ∙
                  ( ap
                    ( concat
                      ( inv
                        ( associative-mul-Wild-Monoid M
                          ( f a)
                          ( map-elim-list-Wild-Monoid x)
                          ( unit-Wild-Monoid M)))
                      ( map-elim-list-Wild-Monoid (cons a x)))
                    ( unit-law-110-associative-Wild-Monoid M
                      ( f a)
                      ( map-elim-list-Wild-Monoid x)))))) ∙
            ( inv
              ( assoc
                ( ap
                  ( mul-Wild-Monoid M (f a))
                  ( preserves-mul-map-elim-list-Wild-Monoid x nil))
                ( inv
                  ( associative-mul-Wild-Monoid M
                    ( f a)
                    ( map-elim-list-Wild-Monoid x)
                    ( unit-Wild-Monoid M)))
                ( right-unit-law-mul-Wild-Monoid M
                  ( map-elim-list-Wild-Monoid (cons a x)))))))))

preserves-coh-unit-laws-map-elim-list-Wild-Monoid :
  {l1 l2 : Level} {X : UU l1} (M : Wild-Monoid l2)
  (f : X → type-Wild-Monoid M) →
  preserves-coherence-unit-laws-mul-pointed-map-H-Space
    ( list-H-Space X)
    ( h-space-Wild-Monoid M)
    ( pointed-map-elim-list-Wild-Monoid M f)
    ( λ {x} {y} → preserves-mul-map-elim-list-Wild-Monoid M f x y)
    ( preserves-left-unit-law-map-elim-list-Wild-Monoid M f)
    ( preserves-right-unit-law-map-elim-list-Wild-Monoid M f)
preserves-coh-unit-laws-map-elim-list-Wild-Monoid
  (pair (pair (pair M eM) (pair μ (pair lM (pair rM cM)))) αM) f = refl

elim-list-Wild-Monoid :
  {l1 l2 : Level} {X : UU l1} (M : Wild-Monoid l2)
  (f : X → type-Wild-Monoid M) →
  hom-Wild-Monoid (list-Wild-Monoid X) M
elim-list-Wild-Monoid M f =
  pair
    ( pair (map-elim-list-Wild-Monoid M f) refl)
    ( pair
      ( λ {x} {y} → preserves-mul-map-elim-list-Wild-Monoid M f x y)
      ( pair (preserves-left-unit-law-map-elim-list-Wild-Monoid M f)
        ( pair
          ( preserves-right-unit-law-map-elim-list-Wild-Monoid M f)
          ( preserves-coh-unit-laws-map-elim-list-Wild-Monoid M f))))
```

### Contractibility of the type `hom (list X) M` of morphisms of wild monoids

This remains to be formalized. The following block contains some abandoned old
code towards this goal:

```text
htpy-elim-list-Wild-Monoid :
  {l1 l2 : Level} {X : UU l1} (M : Wild-Monoid l2)
  (g h : hom-Wild-Monoid (list-Wild-Monoid X) M)
  ( H : ( map-hom-Wild-Monoid (list-Wild-Monoid X) M g ∘ unit-list) ~
        ( map-hom-Wild-Monoid (list-Wild-Monoid X) M h ∘ unit-list)) →
  htpy-hom-Wild-Monoid (list-Wild-Monoid X) M g h
htpy-elim-list-Wild-Monoid {X = X} M g h H =
  pair (pair α β) γ
  where
  α : pr1 (pr1 g) ~ pr1 (pr1 h)
  α nil =
    ( preserves-unit-map-hom-Wild-Monoid (list-Wild-Monoid X) M g) ∙
    ( inv (preserves-unit-map-hom-Wild-Monoid (list-Wild-Monoid X) M h))
  α (cons x l) =
    ( preserves-mul-map-hom-Wild-Monoid
      ( list-Wild-Monoid X)
      ( M)
      ( g)
      ( unit-list x)
      ( l)) ∙
    ( ( ap-mul-Wild-Monoid M (H x) (α l)) ∙
      ( inv
        ( preserves-mul-map-hom-Wild-Monoid
          ( list-Wild-Monoid X)
          ( M)
          ( h)
          ( unit-list x)
          ( l))))
  β : (x y : pr1 (pr1 (list-Wild-Monoid X))) →
    pr2 (pr1 g) x y ∙ ap-mul-Wild-Monoid M (α x) (α y) ＝
    α (concat-list x y) ∙ pr2 (pr1 h) x y
  β nil y = {!!}
  β (cons x x₁) y = {!!}
  γ : pr2 g ＝ α nil ∙ pr2 h
  γ =
    ( inv right-unit) ∙
    ( ( left-whisker-concat (pr2 g) (inv (left-inv (pr2 h)))) ∙
      ( inv (assoc (pr2 g) (inv (pr2 h)) (pr2 h))))
```
