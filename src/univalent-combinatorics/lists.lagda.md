# Lists

```agda
module univalent-combinatorics.lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.monoids
```

</details>

## Idea

The type of lists of elements of a type `A` is defined inductively, with an empty list and an operation that extends a list with one element from `A`.

## Definition

```agda
data list {l : Level} (A : UU l) : UU l where
  nil : list A
  cons : A → list A → list A

in-list : {l : Level} {A : UU l} → A → list A
in-list a = cons a nil
```

## Operations

```agda
fold-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (b : B) (μ : A → (B → B)) →
  list A → B
fold-list b μ nil = b
fold-list b μ (cons a l) = μ a (fold-list b μ l)

map-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  list A → list B
map-list f = fold-list nil (λ a → cons (f a))

length-list : {l : Level} {A : UU l} → list A → ℕ
length-list = fold-list 0 (λ a → succ-ℕ)

sum-list-ℕ : list ℕ → ℕ
sum-list-ℕ = fold-list 0 add-ℕ

product-list-ℕ : list ℕ → ℕ
product-list-ℕ = fold-list 1 mul-ℕ

concat-list : {l : Level} {A : UU l} → list A → (list A → list A)
concat-list {l} {A} = fold-list id (λ a f → (cons a) ∘ f)

flatten-list : {l : Level} {A : UU l} → list (list A) → list A
flatten-list = fold-list nil concat-list

reverse-list : {l : Level} {A : UU l} → list A → list A
reverse-list nil = nil
reverse-list (cons a l) = concat-list (reverse-list l) (in-list a)

data _∈-list_ {l : Level} {A : UU l} : A → list A → UU l where
  is-head : (a : A) (l : list A) → a ∈-list (cons a l)
  is-in-tail : (a x : A) (l : list A) → a ∈-list l → a ∈-list (cons x l)
```

```agda
Eq-list : {l1 : Level} {A : UU l1} → list A → list A → UU l1
Eq-list {l1} nil nil = raise-unit l1
Eq-list {l1} nil (cons x l') = raise-empty l1
Eq-list {l1} (cons x l) nil = raise-empty l1
Eq-list {l1} (cons x l) (cons x' l') = (Id x x') × Eq-list l l'

refl-Eq-list : {l1 : Level} {A : UU l1} (l : list A) → Eq-list l l
refl-Eq-list nil = raise-star
refl-Eq-list (cons x l) = pair refl (refl-Eq-list l)

Eq-eq-list :
  {l1 : Level} {A : UU l1} (l l' : list A) → Id l l' → Eq-list l l'
Eq-eq-list l .l refl = refl-Eq-list l

eq-Eq-list :
  {l1 : Level} {A : UU l1} (l l' : list A) → Eq-list l l' → Id l l'
eq-Eq-list nil nil (map-raise star) = refl
eq-Eq-list nil (cons x l') (map-raise f) = ex-falso f
eq-Eq-list (cons x l) nil (map-raise f) = ex-falso f
eq-Eq-list (cons x l) (cons .x l') (pair refl e) =
  ap (cons x) (eq-Eq-list l l' e)

square-eq-Eq-list :
  {l1 : Level} {A : UU l1} {x : A} {l l' : list A} (p : Id l l') →
  Id (Eq-eq-list (cons x l) (cons x l') (ap (cons x) p))
     (pair refl (Eq-eq-list l l' p))
square-eq-Eq-list refl = refl

issec-eq-Eq-list :
  {l1 : Level} {A : UU l1} (l l' : list A) (e : Eq-list l l') →
  Id (Eq-eq-list l l' (eq-Eq-list l l' e)) e
issec-eq-Eq-list nil nil e = eq-is-contr is-contr-raise-unit
issec-eq-Eq-list nil (cons x l') e = ex-falso (is-empty-raise-empty e)
issec-eq-Eq-list (cons x l) nil e = ex-falso (is-empty-raise-empty e)
issec-eq-Eq-list (cons x l) (cons .x l') (pair refl e) =
  ( square-eq-Eq-list (eq-Eq-list l l' e)) ∙
  ( ap (pair refl) (issec-eq-Eq-list l l' e))

eq-Eq-refl-Eq-list :
  {l1 : Level} {A : UU l1} (l : list A) →
  Id (eq-Eq-list l l (refl-Eq-list l)) refl
eq-Eq-refl-Eq-list nil = refl
eq-Eq-refl-Eq-list (cons x l) = ap (ap (cons x)) (eq-Eq-refl-Eq-list l)

isretr-eq-Eq-list :
  {l1 : Level} {A : UU l1} (l l' : list A) (p : Id l l') →
  Id (eq-Eq-list l l' (Eq-eq-list l l' p)) p
isretr-eq-Eq-list nil .nil refl = refl
isretr-eq-Eq-list (cons x l) .(cons x l) refl = eq-Eq-refl-Eq-list (cons x l)

is-equiv-Eq-eq-list :
  {l1 : Level} {A : UU l1} (l l' : list A) → is-equiv (Eq-eq-list l l')
is-equiv-Eq-eq-list l l' =
  is-equiv-has-inverse
    ( eq-Eq-list l l')
    ( issec-eq-Eq-list l l')
    ( isretr-eq-Eq-list l l')

equiv-Eq-list :
  {l1 : Level} {A : UU l1} (l l' : list A) → Id l l' ≃ Eq-list l l'
equiv-Eq-list l l' =
  pair (Eq-eq-list l l') (is-equiv-Eq-eq-list l l')

is-contr-total-Eq-list :
  {l1 : Level} {A : UU l1} (l : list A) →
  is-contr (Σ (list A) (Eq-list l))
is-contr-total-Eq-list {A = A} l =
  is-contr-equiv'
    ( Σ (list A) (Id l))
    ( equiv-tot (equiv-Eq-list l))
    ( is-contr-total-path l)

is-trunc-Eq-list :
  (k : 𝕋) {l : Level} {A : UU l} → is-trunc (succ-𝕋 (succ-𝕋 k)) A →
  (l l' : list A) → is-trunc (succ-𝕋 k) (Eq-list l l')
is-trunc-Eq-list k H nil nil =
  is-trunc-is-contr (succ-𝕋 k) is-contr-raise-unit
is-trunc-Eq-list k H nil (cons x l') =
  is-trunc-is-empty k is-empty-raise-empty
is-trunc-Eq-list k H (cons x l) nil =
  is-trunc-is-empty k is-empty-raise-empty
is-trunc-Eq-list k H (cons x l) (cons y l') =
  is-trunc-prod (succ-𝕋 k) (H x y) (is-trunc-Eq-list k H l l')

is-trunc-list :
  (k : 𝕋) {l : Level} {A : UU l} → is-trunc (succ-𝕋 (succ-𝕋 k)) A →
  is-trunc (succ-𝕋 (succ-𝕋 k)) (list A)
is-trunc-list k H l l' =
  is-trunc-equiv
    ( succ-𝕋 k)
    ( Eq-list l l')
    ( equiv-Eq-list l l')
    ( is-trunc-Eq-list k H l l')

is-set-list :
  {l : Level} {A : UU l} → is-set A → is-set (list A)
is-set-list = is-trunc-list neg-two-𝕋

list-Set : {l : Level} → Set l → Set l
list-Set A = pair (list (type-Set A)) (is-set-list (is-set-type-Set A))

has-decidable-equality-list :
  {l1 : Level} {A : UU l1} →
  has-decidable-equality A → has-decidable-equality (list A)
has-decidable-equality-list d nil nil = inl refl
has-decidable-equality-list d nil (cons x l) =
  inr (map-inv-raise ∘ Eq-eq-list nil (cons x l))
has-decidable-equality-list d (cons x l) nil =
  inr (map-inv-raise ∘ Eq-eq-list (cons x l) nil)
has-decidable-equality-list d (cons x l) (cons x' l') =
  is-decidable-iff
    ( eq-Eq-list (cons x l) (cons x' l'))
    ( Eq-eq-list (cons x l) (cons x' l'))
    ( is-decidable-prod
      ( d x x')
      ( is-decidable-iff
        ( Eq-eq-list l l')
        ( eq-Eq-list l l')
        ( has-decidable-equality-list d l l')))

is-decidable-left-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable (A × B) → B → is-decidable A
is-decidable-left-factor (inl (pair x y)) b = inl x
is-decidable-left-factor (inr f) b = inr (λ a → f (pair a b))

is-decidable-right-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable (A × B) → A → is-decidable B
is-decidable-right-factor (inl (pair x y)) a = inl y
is-decidable-right-factor (inr f) a = inr (λ b → f (pair a b))

has-decidable-equality-has-decidable-equality-list :
  {l1 : Level} {A : UU l1} →
  has-decidable-equality (list A) → has-decidable-equality A
has-decidable-equality-has-decidable-equality-list d x y =
  is-decidable-left-factor
    ( is-decidable-iff
      ( Eq-eq-list (cons x nil) (cons y nil))
      ( eq-Eq-list (cons x nil) (cons y nil))
      ( d (cons x nil) (cons y nil)))
    ( raise-star)

--------------------------------------------------------------------------------

unit-list :
  {l1 : Level} {A : UU l1} → A → list A
unit-list a = cons a nil

{- First we introduce the functoriality of the list operation, because it will
   come in handy when we try to define and prove more advanced things. -}

functor-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  list A → list B
functor-list f nil = nil
functor-list f (cons a x) = cons (f a) (functor-list f x)

identity-law-functor-list :
  {l1 : Level} {A : UU l1} →
  functor-list (id {A = A}) ~ id
identity-law-functor-list nil = refl
identity-law-functor-list (cons a x) =
  ap (cons a) (identity-law-functor-list x)

composition-law-functor-list :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (f : A → B) (g : B → C) →
  functor-list (g ∘ f) ~ (functor-list g ∘ functor-list f)
composition-law-functor-list f g nil = refl
composition-law-functor-list f g (cons a x) =
  ap (cons (g (f a))) (composition-law-functor-list f g x)

{- Concatenation of lists is an associative operation and nil is the unit for
   list concatenation. -}

assoc-concat-list :
  {l1 : Level} {A : UU l1} (x y z : list A) →
  Id (concat-list (concat-list x y) z) (concat-list x (concat-list y z))
assoc-concat-list nil y z = refl
assoc-concat-list (cons a x) y z = ap (cons a) (assoc-concat-list x y z)

left-unit-law-concat-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (concat-list nil x) x
left-unit-law-concat-list x = refl

right-unit-law-concat-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (concat-list x nil) x
right-unit-law-concat-list nil = refl
right-unit-law-concat-list (cons a x) =
  ap (cons a) (right-unit-law-concat-list x)

list-Monoid : {l : Level} (X : Set l) → Monoid l
list-Monoid X =
  pair
    ( pair (list-Set X) (pair concat-list assoc-concat-list))
    ( pair nil (pair left-unit-law-concat-list right-unit-law-concat-list))

{- The length operation or course behaves well with respect to the other list
   operations. -}

length-nil :
  {l1 : Level} {A : UU l1} →
  Id (length-list {A = A} nil) zero-ℕ
length-nil = refl

length-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id (length-list (concat-list x y)) (add-ℕ (length-list x) (length-list y))
length-concat-list nil y = inv (left-unit-law-add-ℕ (length-list y))
length-concat-list (cons a x) y =
  ( ap succ-ℕ (length-concat-list x y)) ∙
  ( inv (left-successor-law-add-ℕ (length-list x) (length-list y)))

length-functor-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (l : list A) →
  Id (length-list (map-list f l)) (length-list l)
length-functor-list f nil = refl
length-functor-list f (cons x l) =
  ap succ-ℕ (length-functor-list f l)

{- We now prove the properties of flattening. -}

flatten-unit-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (flatten-list (unit-list x)) x
flatten-unit-list x = right-unit-law-concat-list x

length-flatten-list :
  {l1 : Level} {A : UU l1} (x : list (list A)) →
  Id ( length-list (flatten-list x))
     ( sum-list-ℕ (functor-list length-list x))
length-flatten-list nil = refl
length-flatten-list (cons a x) =
  ( length-concat-list a (flatten-list x)) ∙
  ( ap (add-ℕ (length-list a)) (length-flatten-list x))

flatten-concat-list :
  {l1 : Level} {A : UU l1} (x y : list (list A)) →
  Id ( flatten-list (concat-list x y))
     ( concat-list (flatten-list x) (flatten-list y))
flatten-concat-list nil y = refl
flatten-concat-list (cons a x) y =
  ( ap (concat-list a) (flatten-concat-list x y)) ∙
  ( inv (assoc-concat-list a (flatten-list x) (flatten-list y)))

flatten-flatten-list :
  {l1 : Level} {A : UU l1} (x : list (list (list A))) →
  Id ( flatten-list (flatten-list x))
     ( flatten-list (functor-list flatten-list x))
flatten-flatten-list nil = refl
flatten-flatten-list (cons a x) =
  ( flatten-concat-list a (flatten-list x)) ∙
  ( ap (concat-list (flatten-list a)) (flatten-flatten-list x))

{- Next, we prove the basic properties of list reversal. -}

reverse-unit-list :
  {l1 : Level} {A : UU l1} (a : A) →
  Id (reverse-list (unit-list a)) (unit-list a)
reverse-unit-list a = refl

length-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (length-list (reverse-list x)) (length-list x)
length-reverse-list nil = refl
length-reverse-list (cons a x) =
  ( length-concat-list (reverse-list x) (unit-list a)) ∙
  ( ap succ-ℕ (length-reverse-list x))

reverse-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id ( reverse-list (concat-list x y))
     ( concat-list (reverse-list y) (reverse-list x))
reverse-concat-list nil y =
  inv (right-unit-law-concat-list (reverse-list y))
reverse-concat-list (cons a x) y =
  ( ap (λ t → concat-list t (unit-list a)) (reverse-concat-list x y)) ∙
  ( assoc-concat-list (reverse-list y) (reverse-list x) (unit-list a))

reverse-flatten-list :
  {l1 : Level} {A : UU l1} (x : list (list A)) →
  Id ( reverse-list (flatten-list x))
     ( flatten-list (reverse-list (functor-list reverse-list x)))
reverse-flatten-list nil = refl
reverse-flatten-list (cons a x) =
  ( reverse-concat-list a (flatten-list x)) ∙
  ( ( ap (λ t → concat-list t (reverse-list a)) (reverse-flatten-list x)) ∙
    ( ( ap
        ( concat-list
          ( flatten-list (reverse-list (functor-list reverse-list x))))
          ( inv (flatten-unit-list (reverse-list a)))) ∙
      ( inv
        ( flatten-concat-list
          ( reverse-list (functor-list reverse-list x))
          ( unit-list (reverse-list a))))))

reverse-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (reverse-list (reverse-list x)) x
reverse-reverse-list nil = refl
reverse-reverse-list (cons a x) =
  ( reverse-concat-list (reverse-list x) (unit-list a)) ∙
  ( ap (concat-list (unit-list a)) (reverse-reverse-list x))

--------------------------------------------------------------------------------

{- Next we define the head and tail operations, and we define the operations
   of picking and removing the last element from a list. -}

head-list :
  {l1 : Level} {A : UU l1} → list A → list A
head-list nil = nil
head-list (cons a x) = unit-list a

tail-list :
  {l1 : Level} {A : UU l1} → list A → list A
tail-list nil = nil
tail-list (cons a x) = x

last-element-list :
  {l1 : Level} {A : UU l1} → list A → list A
last-element-list nil = nil
last-element-list (cons a nil) = unit-list a
last-element-list (cons a (cons b x)) = last-element-list (cons b x)

remove-last-element-list :
  {l1 : Level} {A : UU l1} → list A → list A
remove-last-element-list nil = nil
remove-last-element-list (cons a nil) = nil
remove-last-element-list (cons a (cons b x)) =
  cons a (remove-last-element-list (cons b x))

cons' :
  {l1 : Level} {A : UU l1} → list A → A → list A
cons' x a = concat-list x (unit-list a)

{- We prove the basic properties about heads and tails and their duals. -}

eta-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (concat-list (head-list x) (tail-list x)) x
eta-list nil = refl
eta-list (cons a x) = refl

eta-list' :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (concat-list (remove-last-element-list x) (last-element-list x)) x
eta-list' nil = refl
eta-list' (cons a nil) = refl
eta-list' (cons a (cons b x)) = ap (cons a) (eta-list' (cons b x))

last-element-cons' :
  {l1 : Level} {A : UU l1} (x : list A) (a : A) →
  Id (last-element-list (cons' x a)) (unit-list a)
last-element-cons' nil a = refl
last-element-cons' (cons b nil) a = refl
last-element-cons' (cons b (cons c x)) a =
  last-element-cons' (cons c x) a

head-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id ( head-list (concat-list x y))
     ( head-list (concat-list (head-list x) (head-list y)))
head-concat-list nil nil = refl
head-concat-list nil (cons x y) = refl
head-concat-list (cons a x) y = refl

tail-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id ( tail-list (concat-list x y))
     ( concat-list (tail-list x) (tail-list (concat-list (head-list x) y)))
tail-concat-list nil y = refl
tail-concat-list (cons a x) y = refl

last-element-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id ( last-element-list (concat-list x y))
     ( last-element-list
       ( concat-list (last-element-list x) (last-element-list y)))
last-element-concat-list nil nil = refl
last-element-concat-list nil (cons b nil) = refl
last-element-concat-list nil (cons b (cons c y)) =
  last-element-concat-list nil (cons c y)
last-element-concat-list (cons a nil) nil = refl
last-element-concat-list (cons a nil) (cons b nil) = refl
last-element-concat-list (cons a nil) (cons b (cons c y)) =
  last-element-concat-list (cons a nil) (cons c y)
last-element-concat-list (cons a (cons b x)) y =
  last-element-concat-list (cons b x) y

remove-last-element-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id ( remove-last-element-list (concat-list x y))
     ( concat-list
       ( remove-last-element-list (concat-list x (head-list y)))
       ( remove-last-element-list y))
remove-last-element-concat-list nil nil = refl
remove-last-element-concat-list nil (cons a nil) = refl
remove-last-element-concat-list nil (cons a (cons b y)) = refl
remove-last-element-concat-list (cons a nil) nil = refl
remove-last-element-concat-list (cons a nil) (cons b y) = refl
remove-last-element-concat-list (cons a (cons b x)) y =
  ap (cons a) (remove-last-element-concat-list (cons b x) y)

head-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (head-list (reverse-list x)) (last-element-list x)
head-reverse-list nil = refl
head-reverse-list (cons a nil) = refl
head-reverse-list (cons a (cons b x)) =
  ( ap head-list
    ( assoc-concat-list (reverse-list x) (unit-list b) (unit-list a))) ∙
  ( ( head-concat-list
      ( reverse-list x)
      ( concat-list (unit-list b) (unit-list a))) ∙
    ( ( inv (head-concat-list (reverse-list x) (unit-list b))) ∙
      ( head-reverse-list (cons b x))))

last-element-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (last-element-list (reverse-list x)) (head-list x)
last-element-reverse-list x =
  ( inv (head-reverse-list (reverse-list x))) ∙
  ( ap head-list (reverse-reverse-list x))

tail-concat-list' :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id ( tail-list (concat-list x y))
     ( concat-list
       ( tail-list x)
       ( tail-list (concat-list (last-element-list x) y)))
tail-concat-list' nil y = refl
tail-concat-list' (cons a nil) y = refl
tail-concat-list' (cons a (cons b x)) y =
  ap (cons b) (tail-concat-list' (cons b x) y)

tail-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (tail-list (reverse-list x)) (reverse-list (remove-last-element-list x))
tail-reverse-list nil = refl
tail-reverse-list (cons a nil) = refl
tail-reverse-list (cons a (cons b x)) =
  ( tail-concat-list' (reverse-list (cons b x)) (unit-list a)) ∙
  ( ( ap
      ( λ t → concat-list
        ( tail-list (reverse-list (cons b x)))
        ( tail-list (concat-list t (unit-list a))))
      ( last-element-cons' (reverse-list x) b)) ∙
    ( ap (λ t → concat-list t (unit-list a)) (tail-reverse-list (cons b x))))

remove-last-element-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (remove-last-element-list (reverse-list x)) (reverse-list (tail-list x))
remove-last-element-reverse-list x =
  ( inv (reverse-reverse-list (remove-last-element-list (reverse-list x)))) ∙
  ( ( inv (ap reverse-list (tail-reverse-list (reverse-list x)))) ∙
    ( ap (reverse-list ∘ tail-list) (reverse-reverse-list x)))

--------------------------------------------------------------------------------

map-algebra-list :
  {l1 : Level} (A : UU l1) →
  unit + (A × list A) → list A
map-algebra-list A (inl star) = nil
map-algebra-list A (inr (pair a x)) = cons a x

inv-map-algebra-list :
  {l1 : Level} (A : UU l1) →
  list A → unit + (A × list A)
inv-map-algebra-list A nil = inl star
inv-map-algebra-list A (cons a x) = inr (pair a x)

issec-inv-map-algebra-list :
  {l1 : Level} (A : UU l1) →
  (map-algebra-list A ∘ inv-map-algebra-list A) ~ id
issec-inv-map-algebra-list A nil = refl
issec-inv-map-algebra-list A (cons a x) = refl

isretr-inv-map-algebra-list :
  {l1 : Level} (A : UU l1) →
  (inv-map-algebra-list A ∘ map-algebra-list A) ~ id
isretr-inv-map-algebra-list A (inl star) = refl
isretr-inv-map-algebra-list A (inr (pair a x)) = refl

is-equiv-map-algebra-list :
  {l1 : Level} (A : UU l1) → is-equiv (map-algebra-list A)
is-equiv-map-algebra-list A =
  is-equiv-has-inverse
    ( inv-map-algebra-list A)
    ( issec-inv-map-algebra-list A)
    ( isretr-inv-map-algebra-list A)
```

### `map-list` preserves concatenation

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  preserves-concat-map-list :
    (l k : list A) →
    Id ( map-list f (concat-list l k))
       ( concat-list (map-list f l) (map-list f k))
  preserves-concat-map-list nil k = refl
  preserves-concat-map-list (cons x l) k =
    ap (cons (f x)) (preserves-concat-map-list l k)

```

### Multiplication of a list of elements in a monoid

```agda
module _
  {l : Level} (M : Monoid l)
  where

  mul-list-Monoid : list (type-Monoid M) → type-Monoid M
  mul-list-Monoid nil = unit-Monoid M
  mul-list-Monoid (cons x l) = mul-Monoid M x (mul-list-Monoid l)

  distributive-mul-list-Monoid :
    (l1 l2 : list (type-Monoid M)) →
    Id ( mul-list-Monoid (concat-list l1 l2))
       ( mul-Monoid M (mul-list-Monoid l1) (mul-list-Monoid l2))
  distributive-mul-list-Monoid nil l2 =
    inv (left-unit-law-mul-Monoid M (mul-list-Monoid l2))
  distributive-mul-list-Monoid (cons x l1) l2 =
    ( ap (mul-Monoid M x) (distributive-mul-list-Monoid l1 l2)) ∙
    ( inv (associative-mul-Monoid M x (mul-list-Monoid l1) (mul-list-Monoid l2)))
```
