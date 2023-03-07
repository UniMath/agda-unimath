# Isolated points

```agda
module foundation.isolated-points where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-embeddings
open import foundation.decidable-equality
open import foundation.decidable-maps
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.maybe
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A point `a : A` is considered to be isolated if `Id a x` is decidable for any `x`.

## Definitions

### Isolated points

```agda
is-isolated :
  {l1 : Level} {X : UU l1} (a : X) → UU l1
is-isolated {l1} {X} a = (x : X) → is-decidable (a ＝ x)

isolated-point :
  {l1 : Level} (X : UU l1) → UU l1
isolated-point X = Σ X is-isolated

module _
  {l : Level} {X : UU l} (x : isolated-point X)
  where

  point-isolated-point : X
  point-isolated-point = pr1 x

  is-isolated-isolated-point : is-isolated point-isolated-point
  is-isolated-isolated-point = pr2 x
```

### Complements of isolated points

```agda
complement-isolated-point :
  {l1 : Level} (X : UU l1) → isolated-point X → UU l1
complement-isolated-point X x =
  Σ X (λ y → ¬ (point-isolated-point x ＝ y))
```

## Properties

### A point is decidable if and only if the constant map pointing at it is decidable

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  is-decidable-map-const-is-isolated :
    is-isolated a → is-decidable-map (const unit A a)
  is-decidable-map-const-is-isolated d x =
    is-decidable-equiv (fib-const a x) (d x)

  is-isolated-is-decidable-map-const :
    is-decidable-map (const unit A a) → is-isolated a
  is-isolated-is-decidable-map-const d x =
    is-decidable-equiv' (fib-const a x) (d x)

  cases-Eq-isolated-point :
    is-isolated a → (x : A) → is-decidable (a ＝ x) → UU lzero
  cases-Eq-isolated-point H x (inl p) = unit
  cases-Eq-isolated-point H x (inr f) = empty

  abstract
    is-prop-cases-Eq-isolated-point :
      (d : is-isolated a) (x : A) (dx : is-decidable (a ＝ x)) →
      is-prop (cases-Eq-isolated-point d x dx)
    is-prop-cases-Eq-isolated-point d x (inl p) = is-prop-unit
    is-prop-cases-Eq-isolated-point d x (inr f) = is-prop-empty

  Eq-isolated-point : is-isolated a → A → UU lzero
  Eq-isolated-point d x = cases-Eq-isolated-point d x (d x)

  abstract
    is-prop-Eq-isolated-point :
      (d : is-isolated a) (x : A) → is-prop (Eq-isolated-point d x)
    is-prop-Eq-isolated-point d x =
      is-prop-cases-Eq-isolated-point d x (d x)

  Eq-isolated-point-Prop : is-isolated a → A → Prop lzero
  pr1 (Eq-isolated-point-Prop d x) = Eq-isolated-point d x
  pr2 (Eq-isolated-point-Prop d x) = is-prop-Eq-isolated-point d x

  decide-reflexivity :
    (d : is-decidable (a ＝ a)) → Σ (a ＝ a) (λ p → inl p ＝ d)
  pr1 (decide-reflexivity (inl p)) = p
  pr2 (decide-reflexivity (inl p)) = refl
  decide-reflexivity (inr f) = ex-falso (f refl)

  abstract
    refl-Eq-isolated-point : (d : is-isolated a) → Eq-isolated-point d a
    refl-Eq-isolated-point d =
      tr ( cases-Eq-isolated-point d a)
        ( pr2 (decide-reflexivity (d a)))
        ( star)

  abstract
    Eq-eq-isolated-point :
      (d : is-isolated a) {x : A} → a ＝ x → Eq-isolated-point d x
    Eq-eq-isolated-point d refl = refl-Eq-isolated-point d

  abstract
    center-total-Eq-isolated-point :
      (d : is-isolated a) → Σ A (Eq-isolated-point d)
    pr1 (center-total-Eq-isolated-point d) = a
    pr2 (center-total-Eq-isolated-point d) = refl-Eq-isolated-point d

    cases-contraction-total-Eq-isolated-point :
      (d : is-isolated a) (x : A) (dx : is-decidable (a ＝ x))
      (e : cases-Eq-isolated-point d x dx) → a ＝ x
    cases-contraction-total-Eq-isolated-point d x (inl p) e = p

    contraction-total-Eq-isolated-point :
      (d : is-isolated a) (t : Σ A (Eq-isolated-point d)) →
      center-total-Eq-isolated-point d ＝ t
    contraction-total-Eq-isolated-point d (pair x e) =
      eq-type-subtype
        ( Eq-isolated-point-Prop d)
        ( cases-contraction-total-Eq-isolated-point d x (d x) e)

    is-contr-total-Eq-isolated-point :
      (d : is-isolated a) → is-contr (Σ A (Eq-isolated-point d))
    pr1 (is-contr-total-Eq-isolated-point d) = center-total-Eq-isolated-point d
    pr2 (is-contr-total-Eq-isolated-point d) =
      contraction-total-Eq-isolated-point d

  abstract
    is-equiv-Eq-eq-isolated-point :
      (d : is-isolated a) (x : A) → is-equiv (Eq-eq-isolated-point d {x})
    is-equiv-Eq-eq-isolated-point d =
      fundamental-theorem-id
        ( is-contr-total-Eq-isolated-point d)
        ( λ x → Eq-eq-isolated-point d {x})

  abstract
    equiv-Eq-eq-isolated-point :
      (d : is-isolated a) (x : A) → (a ＝ x) ≃ Eq-isolated-point d x
    pr1 (equiv-Eq-eq-isolated-point d x) = Eq-eq-isolated-point d
    pr2 (equiv-Eq-eq-isolated-point d x) = is-equiv-Eq-eq-isolated-point d x

  abstract
    is-prop-eq-isolated-point : (d : is-isolated a) (x : A) → is-prop (a ＝ x)
    is-prop-eq-isolated-point d x =
      is-prop-equiv
        ( equiv-Eq-eq-isolated-point d x)
        ( is-prop-Eq-isolated-point d x)

  is-contr-loop-space-isolated-point :
    (d : is-isolated a) → is-contr (a ＝ a)
  is-contr-loop-space-isolated-point d =
    is-proof-irrelevant-is-prop (is-prop-eq-isolated-point d a) refl

  abstract
    is-emb-const-is-isolated : is-isolated a → is-emb (const unit A a)
    is-emb-const-is-isolated d star =
      fundamental-theorem-id
        ( is-contr-equiv
          ( a ＝ a)
          ( left-unit-law-prod)
          ( is-proof-irrelevant-is-prop
            ( is-prop-eq-isolated-point d a)
            ( refl)))
        ( λ x → ap (λ y → a))
```

### Being an isolated point is a property

```agda
is-prop-is-isolated :
  {l1 : Level} {A : UU l1} (a : A) → is-prop (is-isolated a)
is-prop-is-isolated a =
  is-prop-is-inhabited
    ( λ H →
      is-prop-Π (λ x → is-prop-is-decidable (is-prop-eq-isolated-point a H x)))

is-isolated-Prop :
  {l1 : Level} {A : UU l1} (a : A) → Prop l1
pr1 (is-isolated-Prop a) = is-isolated a
pr2 (is-isolated-Prop a) = is-prop-is-isolated a

inclusion-isolated-point :
  {l1 : Level} (A : UU l1) → isolated-point A → A
inclusion-isolated-point A = pr1

is-emb-inclusion-isolated-point :
  {l1 : Level} (A : UU l1) → is-emb (inclusion-isolated-point A)
is-emb-inclusion-isolated-point A = is-emb-inclusion-subtype is-isolated-Prop

has-decidable-equality-isolated-point :
  {l1 : Level} (A : UU l1) → has-decidable-equality (isolated-point A)
has-decidable-equality-isolated-point A (pair x dx) (pair y dy) =
  is-decidable-equiv
    ( equiv-ap-inclusion-subtype is-isolated-Prop)
    ( dx y)

is-set-isolated-point :
  {l1 : Level} (A : UU l1) → is-set (isolated-point A)
is-set-isolated-point A =
  is-set-has-decidable-equality (has-decidable-equality-isolated-point A)

decidable-emb-isolated-point :
  {l1 : Level} {A : UU l1} (a : isolated-point A) → unit ↪d A
decidable-emb-isolated-point {l1} {A} a =
  pair
    ( const unit A (pr1 a))
    ( pair
      ( is-emb-comp
        ( inclusion-isolated-point A)
        ( const unit (isolated-point A) a)
        ( is-emb-inclusion-isolated-point A)
        ( is-emb-is-injective
          ( is-set-isolated-point A)
           λ { {star} {star} p → refl}))
      ( λ x → is-decidable-prod is-decidable-unit (pr2 a x)))
```

### Types with isolated points can be equipped with a Maybe-structure

```agda
map-maybe-structure-isolated-point :
  {l1 : Level} (X : UU l1) (x : isolated-point X) →
  Maybe (complement-isolated-point X x) → X
map-maybe-structure-isolated-point X (pair x d) (inl (pair y f)) = y
map-maybe-structure-isolated-point X (pair x d) (inr star) = x

cases-map-inv-maybe-structure-isolated-point :
  {l1 : Level} (X : UU l1) (x : isolated-point X) →
  (y : X) → is-decidable (pr1 x ＝ y) → Maybe (complement-isolated-point X x)
cases-map-inv-maybe-structure-isolated-point X (pair x dx) y (inl p) =
  inr star
cases-map-inv-maybe-structure-isolated-point X (pair x dx) y (inr f) =
  inl (pair y f)

map-inv-maybe-structure-isolated-point :
  {l1 : Level} (X : UU l1) (x : isolated-point X) →
  X → Maybe (complement-isolated-point X x)
map-inv-maybe-structure-isolated-point X (pair x d) y =
  cases-map-inv-maybe-structure-isolated-point X (pair x d) y (d y)

cases-issec-map-inv-maybe-structure-isolated-point :
  {l1 : Level} (X : UU l1) (x : isolated-point X) →
  (y : X) (d : is-decidable (pr1 x ＝ y)) →
  ( map-maybe-structure-isolated-point X x
    ( cases-map-inv-maybe-structure-isolated-point X x y d)) ＝
  ( y)
cases-issec-map-inv-maybe-structure-isolated-point X (pair x dx) .x (inl refl) =
  refl
cases-issec-map-inv-maybe-structure-isolated-point X (pair x dx) y (inr f) =
  refl

issec-map-inv-maybe-structure-isolated-point :
  {l1 : Level} (X : UU l1) (x : isolated-point X) →
  ( map-maybe-structure-isolated-point X x ∘
    map-inv-maybe-structure-isolated-point X x) ~ id
issec-map-inv-maybe-structure-isolated-point X (pair x d) y =
  cases-issec-map-inv-maybe-structure-isolated-point X (pair x d) y (d y)

isretr-map-inv-maybe-structure-isolated-point :
  {l1 : Level} (X : UU l1) (x : isolated-point X) →
  ( map-inv-maybe-structure-isolated-point X x ∘
    map-maybe-structure-isolated-point X x) ~ id
isretr-map-inv-maybe-structure-isolated-point X (pair x dx) (inl (pair y f)) =
  ap ( cases-map-inv-maybe-structure-isolated-point X (pair x dx) y)
     ( eq-is-prop (is-prop-is-decidable (is-prop-eq-isolated-point x dx y)))
isretr-map-inv-maybe-structure-isolated-point X (pair x dx) (inr star) =
  ap ( cases-map-inv-maybe-structure-isolated-point X (pair x dx) x)
     { x = dx (map-maybe-structure-isolated-point X (pair x dx) (inr star))}
     { y = inl refl}
     ( eq-is-prop (is-prop-is-decidable (is-prop-eq-isolated-point x dx x)))

is-equiv-map-maybe-structure-isolated-point :
  {l1 : Level} (X : UU l1) (x : isolated-point X) →
  is-equiv (map-maybe-structure-isolated-point X x)
is-equiv-map-maybe-structure-isolated-point X x =
  is-equiv-has-inverse
    ( map-inv-maybe-structure-isolated-point X x)
    ( issec-map-inv-maybe-structure-isolated-point X x)
    ( isretr-map-inv-maybe-structure-isolated-point X x)

equiv-maybe-structure-isolated-point :
  {l1 : Level} (X : UU l1) (x : isolated-point X) →
  Maybe (complement-isolated-point X x) ≃ X
equiv-maybe-structure-isolated-point X x =
  pair ( map-maybe-structure-isolated-point X x)
       ( is-equiv-map-maybe-structure-isolated-point X x)

maybe-structure-isolated-point :
  {l1 : Level} {X : UU l1} → isolated-point X → maybe-structure X
maybe-structure-isolated-point {l1} {X} x =
  pair ( complement-isolated-point X x)
       ( equiv-maybe-structure-isolated-point X x)
```

```agda
equiv-complement-isolated-point :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) (x : isolated-point X)
  (y : isolated-point Y) (p : map-equiv e (pr1 x) ＝ pr1 y) →
  complement-isolated-point X x ≃ complement-isolated-point Y y
equiv-complement-isolated-point e x y p =
  equiv-Σ
    ( λ z → ¬ (pr1 y ＝ z))
    ( e)
    ( λ z →
      equiv-neg
        ( equiv-concat (inv p) (map-equiv e z) ∘e (equiv-ap e (pr1 x) z)))
```

```agda
inclusion-complement-isolated-point :
  {l1 : Level} {X : UU l1} (x : isolated-point X) →
  complement-isolated-point X x → X
inclusion-complement-isolated-point x = pr1

natural-inclusion-equiv-complement-isolated-point :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) (x : isolated-point X)
  (y : isolated-point Y) (p : map-equiv e (pr1 x) ＝ pr1 y) →
  ( inclusion-complement-isolated-point y ∘
    map-equiv (equiv-complement-isolated-point e x y p)) ~
  ( map-equiv e ∘ inclusion-complement-isolated-point x)
natural-inclusion-equiv-complement-isolated-point e x y p (pair x' f) = refl
```
