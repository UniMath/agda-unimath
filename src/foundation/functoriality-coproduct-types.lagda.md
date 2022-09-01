---
title: Functoriality of coproduct types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.functoriality-coproduct-types where

open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using (is-contr; is-contr-equiv)
open import foundation.coproduct-types using
  ( _+_; inl; inr; is-injective-inl; neq-inr-inl)
open import foundation.dependent-pair-types using (pair; pr1; pr2; Σ)
open import foundation.equality-coproduct-types using
  ( compute-eq-coprod-inl-inl; compute-eq-coprod-inr-inr;
    map-compute-eq-coprod-inl-inl; is-empty-eq-coprod-inr-inl;
    is-empty-eq-coprod-inl-inr; map-compute-eq-coprod-inr-inr)
open import foundation.equivalences using
  ( htpy-equiv; inv-equiv; is-equiv; is-equiv-has-inverse; map-equiv; 
    map-inv-equiv; left-inverse-law-equiv; right-inverse-law-equiv; _≃_; _∘e_;
    is-equiv-map-equiv)
open import foundation.empty-types using (ex-falso)
open import foundation.fibers-of-maps using (fib)
open import foundation.function-extensionality using (equiv-funext)
open import foundation.functions using (id; _∘_)
open import foundation.functoriality-cartesian-product-types using (equiv-prod)
open import foundation.functoriality-dependent-function-types using
  ( equiv-map-Π)
open import foundation.functoriality-dependent-pair-types using (equiv-tot)
open import foundation.homotopies using
  ( _~_; inv-htpy; _∙h_; is-contr-total-htpy'; refl-htpy)
open import foundation.identity-types using (_＝_; inv; refl; ap; _∙_)
open import foundation.injective-maps using (is-injective-map-equiv)
open import foundation.negation using (¬)
open import foundation.structure-identity-principle using
  ( is-contr-total-Eq-structure)
open import foundation.universal-property-coproduct-types using
  ( equiv-dependent-universal-property-coprod)
open import foundation.universe-levels using (Level; UU)
```

## Idea

Any two maps `f : A → B` and `g : C → D` induce a map `map-coprod f g : coprod A B → coprod C D`.

## Definitions

### The functorial action of the coproduct operation 

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  where
  
  map-coprod : (A → A') → (B → B') → A + B → A' + B'
  map-coprod f g (inl x) = inl (f x)
  map-coprod f g (inr y) = inr (g y)
```

## Properties

### Functoriality of coproducts preserves identity maps

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where
  
  id-map-coprod : (map-coprod (id {A = A}) (id {A = B})) ~ id
  id-map-coprod (inl x) = refl
  id-map-coprod (inr x) = refl
```

### Functoriality of coproducts preserves composition

```agda
module _
  {l1 l2 l1' l2' l1'' l2'' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {A'' : UU l1''} {B'' : UU l2''}
  (f : A → A') (f' : A' → A'') (g : B → B') (g' : B' → B'')
  where
  
  compose-map-coprod :
    (map-coprod (f' ∘ f) (g' ∘ g)) ~ ((map-coprod f' g') ∘ (map-coprod f g))
  compose-map-coprod (inl x) = refl
  compose-map-coprod (inr y) = refl
```

### Functoriality of coproducts preserves homotopies

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {f f' : A → A'} (H : f ~ f') {g g' : B → B'} (K : g ~ g')
  where
  
  htpy-map-coprod : (map-coprod f g) ~ (map-coprod f' g')
  htpy-map-coprod (inl x) = ap inl (H x)
  htpy-map-coprod (inr y) = ap inr (K y)
```

### The fibers of `map-coprod`

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  (f : A' → A) (g : B' → B)
  where

  fib-map-coprod-inl-fib : (x : A) → fib f x → fib (map-coprod f g) (inl x)
  pr1 (fib-map-coprod-inl-fib x (pair a' p)) = inl a'
  pr2 (fib-map-coprod-inl-fib x (pair a' p)) = ap inl p

  fib-fib-map-coprod-inl : (x : A) → fib (map-coprod f g) (inl x) → fib f x
  fib-fib-map-coprod-inl x (pair (inl a') p) =
    pair a' (map-compute-eq-coprod-inl-inl (f a') x p)
  fib-fib-map-coprod-inl x (pair (inr b') p) =
    ex-falso (is-empty-eq-coprod-inr-inl (g b') x p)

  abstract
    issec-fib-fib-map-coprod-inl :
      (x : A) → (fib-map-coprod-inl-fib x ∘ fib-fib-map-coprod-inl x) ~ id
    issec-fib-fib-map-coprod-inl .(f a') (pair (inl a') refl) = refl
    issec-fib-fib-map-coprod-inl x (pair (inr b') p) =
      ex-falso (is-empty-eq-coprod-inr-inl (g b') x p)

  abstract
    isretr-fib-fib-map-coprod-inl :
      (x : A) → (fib-fib-map-coprod-inl x ∘ fib-map-coprod-inl-fib x) ~ id
    isretr-fib-fib-map-coprod-inl .(f a') (pair a' refl) = refl

  abstract
    is-equiv-fib-map-coprod-inl-fib :
      (x : A) → is-equiv (fib-map-coprod-inl-fib x)
    is-equiv-fib-map-coprod-inl-fib x =
      is-equiv-has-inverse
        ( fib-fib-map-coprod-inl x)
        ( issec-fib-fib-map-coprod-inl x)
        ( isretr-fib-fib-map-coprod-inl x)

  fib-map-coprod-inr-fib : (y : B) → fib g y → fib (map-coprod f g) (inr y)
  pr1 (fib-map-coprod-inr-fib y (pair b' p)) = inr b'
  pr2 (fib-map-coprod-inr-fib y (pair b' p)) = ap inr p
  
  fib-fib-map-coprod-inr : (y : B) → fib (map-coprod f g) (inr y) → fib g y
  fib-fib-map-coprod-inr y (pair (inl a') p) =
    ex-falso (is-empty-eq-coprod-inl-inr (f a') y p)
  pr1 (fib-fib-map-coprod-inr y (pair (inr b') p)) = b'
  pr2 (fib-fib-map-coprod-inr y (pair (inr b') p)) =
    map-compute-eq-coprod-inr-inr (g b') y p

  abstract
    issec-fib-fib-map-coprod-inr :
      (y : B) → (fib-map-coprod-inr-fib y ∘ fib-fib-map-coprod-inr y) ~ id
    issec-fib-fib-map-coprod-inr .(g b') (pair (inr b') refl) = refl
    issec-fib-fib-map-coprod-inr y (pair (inl a') p) =
      ex-falso (is-empty-eq-coprod-inl-inr (f a') y p)

  abstract
    isretr-fib-fib-map-coprod-inr :
      (y : B) → (fib-fib-map-coprod-inr y ∘ fib-map-coprod-inr-fib y) ~ id
    isretr-fib-fib-map-coprod-inr .(g b') (pair b' refl) = refl

  abstract
    is-equiv-fib-map-coprod-inr-fib :
      (y : B) → is-equiv (fib-map-coprod-inr-fib y)
    is-equiv-fib-map-coprod-inr-fib y =
      is-equiv-has-inverse
        ( fib-fib-map-coprod-inr y)
        ( issec-fib-fib-map-coprod-inr y)
        ( isretr-fib-fib-map-coprod-inr y)
```

### Functoriality of coproducts preserves equivalences

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  where

  abstract
    is-equiv-map-coprod :
      {f : A → A'} {g : B → B'} →
      is-equiv f → is-equiv g → is-equiv (map-coprod f g)
    pr1
      ( pr1
        ( is-equiv-map-coprod
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) = map-coprod sf sg
    pr2
      ( pr1
        ( is-equiv-map-coprod {f} {g}
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) =
      ( ( inv-htpy (compose-map-coprod sf f sg g)) ∙h
        ( htpy-map-coprod Sf Sg)) ∙h
      ( id-map-coprod A' B')
    pr1
      ( pr2
        ( is-equiv-map-coprod
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) = map-coprod rf rg
    pr2
      ( pr2
        ( is-equiv-map-coprod {f} {g}
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) =
      ( ( inv-htpy (compose-map-coprod f rf g rg)) ∙h
        ( htpy-map-coprod Rf Rg)) ∙h
      ( id-map-coprod A B)

  map-equiv-coprod :
    (A ≃ A') → (B ≃ B') → A + B → A' + B'
  map-equiv-coprod e e' = map-coprod (map-equiv e) (map-equiv e')
  
  equiv-coprod :
    (A ≃ A') → (B ≃ B') → (A + B) ≃ (A' + B')
  pr1 (equiv-coprod e e') = map-equiv-coprod e e'
  pr2 (equiv-coprod e e') =
    is-equiv-map-coprod (is-equiv-map-equiv e) (is-equiv-map-equiv e')
```

### For any two maps `f : A → B` and `g : C → D`, there is at most one pair of maps `f' : A → B` and `g' : C → D` such that `f' + g' = f + g`.

```agda
is-contr-fib-map-coprod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) →
  is-contr
    ( fib ( λ (fg' : (A → B) × (C → D)) → map-coprod (pr1 fg') (pr2 fg'))
          ( map-coprod f g))
is-contr-fib-map-coprod {A = A} {B} {C} {D} f g =
  is-contr-equiv
    ( Σ ( (A → B) × (C → D))
        ( λ fg' →
          ((a : A) → pr1 fg' a ＝ f a) × ((c : C) → pr2 fg' c ＝ g c)))
    ( equiv-tot
      ( λ fg' →
        ( ( equiv-prod
            ( equiv-map-Π
              ( λ a → compute-eq-coprod-inl-inl (pr1 fg' a) (f a)))
            ( equiv-map-Π
              ( λ c → compute-eq-coprod-inr-inr (pr2 fg' c) (g c)))) ∘e
          ( equiv-dependent-universal-property-coprod
            ( λ x →
              map-coprod (pr1 fg') (pr2 fg') x ＝ map-coprod f g x))) ∘e
        ( equiv-funext)))
    ( is-contr-total-Eq-structure
      ( λ f' g' (H : f' ~ f) → (c : C) → g' c ＝ g c)
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
-}
```

### For any equivalence `f : A + B ≃ A + B` and `g : B ≃ B` such that `f` and `g` coincide on `B`, we construct an `h : A ≃ A` such that `htpy-equiv (equiv-coprod h d) f`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} 
  where

  equiv-coproduct-induce-equiv-disjoint :
    (f : (A + B) ≃ (A + B)) (g : B ≃ B)
    (p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b))
    (x : A) (y : B) → ¬ (map-equiv f (inl x) ＝ inr y)
  equiv-coproduct-induce-equiv-disjoint f g p x y q =
    neq-inr-inl
      ( is-injective-map-equiv f
        ( ( p (map-equiv (inv-equiv g) y) ∙
          ( ( ap (λ z → inr (map-equiv z y)) (right-inverse-law-equiv g)) ∙
            ( inv q)))))

  inv-commutative-square-inr :
    (f : (A + B) ≃ (A + B)) (g : B ≃ B)
    (p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b)) →
    (b : B) → map-inv-equiv f (inr b) ＝ inr (map-inv-equiv g b)
  inv-commutative-square-inr f g p b =
    is-injective-map-equiv f
      ( ( ap (λ z → map-equiv z (inr b)) (right-inverse-law-equiv f)) ∙
        ( ( inv (ap (λ z → inr (map-equiv z b)) (right-inverse-law-equiv g))) ∙
          ( inv (p (map-inv-equiv g b)))))
  
  cases-retr-equiv-coprod :
    (f : (A + B) ≃ (A + B)) (g : B ≃ B)
    (p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b))
    (x : A) (y : A + B) → map-equiv f (inl x) ＝ y → A
  cases-retr-equiv-coprod f g p x (inl y) q = y
  cases-retr-equiv-coprod f g p x (inr y) q =
    ex-falso (equiv-coproduct-induce-equiv-disjoint f g p x y q)
  
  inv-cases-retr-equiv-coprod :
    (f : (A + B) ≃ (A + B)) (g : B ≃ B)
    (p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b))
    (x : A) (y : A + B) → map-inv-equiv f (inl x) ＝ y → A
  inv-cases-retr-equiv-coprod f g p =
    cases-retr-equiv-coprod
      ( inv-equiv f)
      ( inv-equiv g)
      ( inv-commutative-square-inr f g p)

  retr-cases-retr-equiv-coprod :
    (f : (A + B) ≃ (A + B)) (g : B ≃ B)
    (p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b))
    (x : A) (y z : A + B) (q : map-equiv f (inl x) ＝ y)
    (r : map-inv-equiv f (inl (cases-retr-equiv-coprod f g p x y q)) ＝ z) →
    ( inv-cases-retr-equiv-coprod f g p
      ( cases-retr-equiv-coprod f g p x y q) z r) ＝
    ( x)   
  retr-cases-retr-equiv-coprod f g p x (inl y) (inl z) q r =
    is-injective-inl
      ( ( inv r) ∙
        ( ( ap (map-inv-equiv f) (inv q)) ∙
          ( ap (λ w → map-equiv w (inl x)) (left-inverse-law-equiv f))))
  retr-cases-retr-equiv-coprod f g p x (inl y) (inr z) q r =
    ex-falso
      ( equiv-coproduct-induce-equiv-disjoint
        ( inv-equiv f)
        ( inv-equiv g)
        ( inv-commutative-square-inr f g p)
        ( y)
        ( z)
        ( r)) 
  retr-cases-retr-equiv-coprod f g p x (inr y) z q r =
    ex-falso (equiv-coproduct-induce-equiv-disjoint f g p x y q)

  sec-cases-retr-equiv-coprod :
    (f : (A + B) ≃ (A + B)) (g : B ≃ B)
    (p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b))
    (x : A) (y z : A + B) (q : map-inv-equiv f (inl x) ＝ y)
    (r : map-equiv f (inl (inv-cases-retr-equiv-coprod f g p x y q)) ＝ z) →
    ( cases-retr-equiv-coprod f g p
      ( inv-cases-retr-equiv-coprod f g p x y q) z r) ＝
    ( x)   
  sec-cases-retr-equiv-coprod f g p x (inl y) (inl z) q r =
    is-injective-inl
      ( ( inv r) ∙
        ( ( ap (map-equiv f) (inv q)) ∙
          ( ap (λ w → map-equiv w (inl x)) (right-inverse-law-equiv f))))
  sec-cases-retr-equiv-coprod f g p x (inl y) (inr z) q r =
    ex-falso (equiv-coproduct-induce-equiv-disjoint f g p y z r)
  sec-cases-retr-equiv-coprod f g p x (inr y) z q r =
    ex-falso
      ( equiv-coproduct-induce-equiv-disjoint
        ( inv-equiv f)
        ( inv-equiv g)
        ( inv-commutative-square-inr f g p)
        ( x)
        ( y)
        ( q))

  retr-equiv-coprod :
    (f : (A + B) ≃ (A + B)) (g : B ≃ B)
    (p : (b : B) → map-equiv f (inr b) ＝ inr (map-equiv g b)) →
    Σ (A ≃ A) (λ h → htpy-equiv f (equiv-coprod h g))
  pr1 (pr1 (retr-equiv-coprod f g p)) x =
    cases-retr-equiv-coprod f g p x (map-equiv f (inl x)) refl
  pr2 (pr1 (retr-equiv-coprod f g p)) =
    is-equiv-has-inverse
      ( λ x →
        inv-cases-retr-equiv-coprod f g p x (map-inv-equiv f (inl x)) refl)
      ( λ x →
        sec-cases-retr-equiv-coprod f g p x
          ( map-inv-equiv f (inl x))
          ( map-equiv f
            ( inl
              ( inv-cases-retr-equiv-coprod f g p x
                ( map-inv-equiv f (inl x))
                ( refl))))
          ( refl)
          ( refl))
      ( λ x →
        retr-cases-retr-equiv-coprod f g p x
          ( map-equiv f (inl x))
          ( map-inv-equiv f
            ( inl
              ( cases-retr-equiv-coprod f g p x
                ( map-equiv f (inl x))
                ( refl))))
          ( refl)
          ( refl))
  pr2 (retr-equiv-coprod f g p) (inl x) =
    commutative-square-inl-retr-equiv-coprod x (map-equiv f (inl x)) refl
    where
    commutative-square-inl-retr-equiv-coprod :
      (x : A) (y : A + B) (q : map-equiv f (inl x) ＝ y) →
      map-equiv f (inl x) ＝ inl (cases-retr-equiv-coprod f g p x y q)
    commutative-square-inl-retr-equiv-coprod x (inl y) q = q
    commutative-square-inl-retr-equiv-coprod x (inr y) q =
      ex-falso (equiv-coproduct-induce-equiv-disjoint f g p x y q)
  pr2 (retr-equiv-coprod f g p) (inr x) = p x
```
