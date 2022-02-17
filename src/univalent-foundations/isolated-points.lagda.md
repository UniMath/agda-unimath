# Isolated points

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-foundations.isolated-points where

open import foundation
open import elementary-number-theory
open import univalent-combinatorics

{-------------------------------------------------------------------------------

  Isolated points
  ---------------

  We introduced isolated points in exercise 12.12

-------------------------------------------------------------------------------}

-- Being isolated is a proposition

--------------------------------------------------------------------------------

-- Complements of isolated points

complement-isolated-point :
  {l1 : Level} (X : UU l1) → isolated-point X → UU l1
complement-isolated-point X x =
  Σ X (λ y → ¬ (Id (pr1 x) y))

--------------------------------------------------------------------------------

-- Maybe structure on a type

maybe-structure :
  {l1 : Level} (X : UU l1) → UU (lsuc l1)
maybe-structure {l1} X = Σ (UU l1) (λ Y → Maybe Y ≃ X)

equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) → Maybe X ≃ Maybe Y
equiv-Maybe e = equiv-coprod e id-equiv

equiv-maybe-structure :
  {l1 : Level} {X : UU l1} (Y Z : maybe-structure X) → UU l1
equiv-maybe-structure Y Z =
  Σ (pr1 Y ≃ pr1 Z) (λ e → htpy-equiv (pr2 Y) (pr2 Z ∘e equiv-Maybe e))

id-equiv-maybe-structure :
  {l1 : Level} {X : UU l1} (Y : maybe-structure X) → equiv-maybe-structure Y Y
id-equiv-maybe-structure Y =
  pair id-equiv (ind-Maybe (pair refl-htpy refl))

equiv-eq-maybe-structure :
  {l1 : Level} {X : UU l1} (Y Z : maybe-structure X) →
  Id Y Z → equiv-maybe-structure Y Z
equiv-eq-maybe-structure Y .Y refl = id-equiv-maybe-structure Y

is-contr-fib-map-coprod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) →
  is-contr
    ( fib ( λ (fg' : (A → B) × (C → D)) → map-coprod (pr1 fg') (pr2 fg'))
          ( map-coprod f g))
is-contr-fib-map-coprod {A = A} {B} {C} {D} f g =
  is-contr-equiv
    ( Σ ( (A → B) × (C → D))
        ( λ fg' → ((a : A) → Id (pr1 fg' a) (f a)) ×
                  ((c : C) → Id (pr2 fg' c) (g c))))
    ( equiv-tot
      ( λ fg' →
        ( ( equiv-prod
            ( equiv-map-Π
              ( λ a → compute-eq-coprod-inl-inl (pr1 fg' a) (f a)))
            ( equiv-map-Π
              ( λ c → compute-eq-coprod-inr-inr (pr2 fg' c) (g c)))) ∘e
          ( equiv-dependent-universal-property-coprod
            ( λ x →
              Id (map-coprod (pr1 fg') (pr2 fg') x) (map-coprod f g x)))) ∘e
        ( equiv-funext)))
    ( is-contr-total-Eq-structure
      ( λ f' g' (H : f' ~ f) → (c : C) → Id (g' c) (g c))
      ( is-contr-total-htpy' f)
      ( pair f refl-htpy)
      ( is-contr-total-htpy' g))

{-
is-emb-map-coprod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} → 
  is-emb (λ (fg : (A → B) × (C → D)) → map-coprod (pr1 fg) (pr2 fg))
is-emb-map-coprod (pair f g) =
  fundamental-theorem-id (pair f g)
    ( refl)
    {! is-contr-fib-map-coprod f g!}
    {!!}

is-contr-total-equiv-maybe-structure :
  {l1 : Level} {X : UU l1} (Y : maybe-structure X) →
  is-contr (Σ (maybe-structure X) (equiv-maybe-structure Y))
is-contr-total-equiv-maybe-structure Y =
  is-contr-total-Eq-structure
    ( λ Z α e → htpy-equiv (pr2 Y) (α ∘e equiv-coprod e id-equiv))
    ( is-contr-total-equiv (pr1 Y))
    ( pair (pr1 Y) id-equiv)
    {!!}
-}

map-maybe-structure-isolated-point :
  {l1 : Level} (X : UU l1) (x : isolated-point X) →
  Maybe (complement-isolated-point X x) → X
map-maybe-structure-isolated-point X (pair x d) (inl (pair y f)) = y
map-maybe-structure-isolated-point X (pair x d) (inr star) = x

cases-map-inv-maybe-structure-isolated-point :
  {l1 : Level} (X : UU l1) (x : isolated-point X) →
  (y : X) → is-decidable (Id (pr1 x) y) → Maybe (complement-isolated-point X x)
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
  (y : X) (d : is-decidable (Id (pr1 x) y)) →
  Id ( map-maybe-structure-isolated-point X x
       ( cases-map-inv-maybe-structure-isolated-point X x y d))
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

equiv-neg :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  (X ≃ Y) → (¬ X ≃ ¬ Y)
equiv-neg {l1} {l2} {X} {Y} e =
  equiv-iff'
    ( neg-Prop' X)
    ( neg-Prop' Y)
    ( pair (map-neg (map-inv-equiv e)) (map-neg (map-equiv e)))

equiv-complement-isolated-point :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) (x : isolated-point X)
  (y : isolated-point Y) (p : Id (map-equiv e (pr1 x)) (pr1 y)) →
  complement-isolated-point X x ≃ complement-isolated-point Y y
equiv-complement-isolated-point e x y p =
  equiv-Σ
    ( λ z → ¬ (Id (pr1 y) z))
    ( e)
    ( λ z →
      equiv-neg
        ( equiv-concat (inv p) (map-equiv e z) ∘e (equiv-ap e (pr1 x) z)))

complement-point-UU-Fin-Level :
  {l1 : Level} {k : ℕ} →
  Σ (UU-Fin-Level l1 (succ-ℕ k)) type-UU-Fin-Level → UU-Fin-Level l1 k
complement-point-UU-Fin-Level {l1} {k} T =
  pair
    ( X')
    ( apply-universal-property-trunc-Prop H (mere-equiv-Prop (Fin k) X')
      ( λ e →
        unit-trunc-Prop
          ( equiv-equiv-Maybe
            { X = Fin k}
            { Y = X'}
            ( ( inv-equiv
                ( equiv-maybe-structure-isolated-point X isolated-x)) ∘e
              ( e)))))
  where
  X = pr1 (pr1 T)
  H = pr2 (pr1 T)
  x = pr2 T
  isolated-x : isolated-point X
  isolated-x = pair x (λ y → has-decidable-equality-has-cardinality H x y)
  X' : UU l1
  X' = complement-isolated-point X isolated-x

complement-point-UU-Fin :
  {k : ℕ} → Σ (UU-Fin (succ-ℕ k)) type-UU-Fin → UU-Fin k
complement-point-UU-Fin X = complement-point-UU-Fin-Level X

type-complement-point-UU-Fin-Level :
  {l1 : Level} {k : ℕ} →
  Σ (UU-Fin-Level l1 (succ-ℕ k)) type-UU-Fin-Level → UU l1
type-complement-point-UU-Fin-Level X =
  type-UU-Fin-Level (complement-point-UU-Fin-Level X)

type-complement-point-UU-Fin :
  {k : ℕ} → Σ (UU-Fin (succ-ℕ k)) type-UU-Fin → UU lzero
type-complement-point-UU-Fin X =
  type-complement-point-UU-Fin-Level X

inclusion-complement-isolated-point :
  {l1 : Level} {X : UU l1} (x : isolated-point X) →
  complement-isolated-point X x → X
inclusion-complement-isolated-point x = pr1

natural-inclusion-equiv-complement-isolated-point :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) (x : isolated-point X)
  (y : isolated-point Y) (p : Id (map-equiv e (pr1 x)) (pr1 y)) →
  ( inclusion-complement-isolated-point y ∘
    map-equiv (equiv-complement-isolated-point e x y p)) ~
  ( map-equiv e ∘ inclusion-complement-isolated-point x)
natural-inclusion-equiv-complement-isolated-point e x y p (pair x' f) = refl

inclusion-complement-point-UU-Fin-Level :
  {l1 : Level} {k : ℕ} (X : Σ (UU-Fin-Level l1 (succ-ℕ k)) type-UU-Fin-Level) →
  type-complement-point-UU-Fin-Level X → type-UU-Fin-Level (pr1 X)
inclusion-complement-point-UU-Fin-Level X = pr1

inclusion-complement-point-UU-Fin :
  {k : ℕ} (X : Σ (UU-Fin (succ-ℕ k)) type-UU-Fin) →
  type-complement-point-UU-Fin X → type-UU-Fin (pr1 X)
inclusion-complement-point-UU-Fin X =
  inclusion-complement-point-UU-Fin-Level X

equiv-complement-point-UU-Fin-Level :
  {l1 : Level} {k : ℕ}
  (X Y : Σ (UU-Fin-Level l1 (succ-ℕ k)) type-UU-Fin-Level) →
  (e : equiv-UU-Fin-Level (pr1 X) (pr1 Y))
  (p : Id (map-equiv e (pr2 X)) (pr2 Y)) →
  equiv-UU-Fin-Level
    ( complement-point-UU-Fin-Level X)
    ( complement-point-UU-Fin-Level Y)
equiv-complement-point-UU-Fin-Level
  S T e p =
  equiv-complement-isolated-point e
    ( pair x (λ x' → has-decidable-equality-has-cardinality H x x'))
    ( pair y (λ y' → has-decidable-equality-has-cardinality K y y'))
    ( p)
  where
  H = pr2 (pr1 S)
  x = pr2 S
  K = pr2 (pr1 T)
  y = pr2 T

equiv-complement-point-UU-Fin :
  {k : ℕ} (X Y : Σ (UU-Fin (succ-ℕ k)) type-UU-Fin) →
  (e : equiv-UU-Fin (pr1 X) (pr1 Y)) (p : Id (map-equiv e (pr2 X)) (pr2 Y)) →
  equiv-UU-Fin (complement-point-UU-Fin X) (complement-point-UU-Fin Y)
equiv-complement-point-UU-Fin X Y e p =
  equiv-complement-point-UU-Fin-Level X Y e p

```
