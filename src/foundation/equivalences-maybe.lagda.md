# Equivalences on Maybe

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.equivalences-maybe where

open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (_↪_; map-emb)
open import foundation.empty-types using (ex-falso)
open import foundation.equivalences using
  ( _≃_; map-equiv; inv-equiv; map-inv-equiv; issec-map-inv-equiv;
    isretr-map-inv-equiv; is-equiv; is-equiv-has-inverse)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (Id; _∙_; inv; refl; ap)
open import foundation.injective-maps using
  ( is-injective; is-injective-map-equiv; is-injective-emb)
open import foundation.maybe using
  ( Maybe; is-exception-Maybe; is-not-exception-Maybe; exception-Maybe;
    is-not-exception-unit-Maybe; is-value-Maybe; value-is-value-Maybe;
    is-value-is-not-exception-Maybe; eq-is-value-Maybe;
    is-decidable-is-exception-Maybe; is-injective-unit-Maybe;
    is-not-exception-is-value-Maybe)
open import foundation.unit-type using (unit; star)
open import foundation.universe-levels using (Level; UU)
```

## Idea

For any two types `X` and `Y`, we have `(X ≃ Y) ↔ (Maybe X ≃ Maybe Y)`.


```agda
-- Proposition 16.2.1 Step (i) of the proof

-- If f is an injective map and f (inl x) is an exception, then f exception is
-- not an exception.

abstract
  is-not-exception-injective-map-exception-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
    is-injective f → (x : X) → is-exception-Maybe (f (inl x)) →
    is-not-exception-Maybe (f exception-Maybe)
  is-not-exception-injective-map-exception-Maybe is-inj-f x p q =
    is-not-exception-unit-Maybe x (is-inj-f (p ∙ inv q))

abstract
  is-not-exception-map-equiv-exception-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
    is-exception-Maybe (map-equiv e (inl x)) →
    is-not-exception-Maybe (map-equiv e exception-Maybe)
  is-not-exception-map-equiv-exception-Maybe e =
    is-not-exception-injective-map-exception-Maybe (is-injective-map-equiv e)

-- If f is injective and f (inl x) is an exception, then f exception is a value
is-value-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) → is-exception-Maybe (f (inl x)) →
  is-value-Maybe (f exception-Maybe)
is-value-injective-map-exception-Maybe {f = f} is-inj-f x H =
  is-value-is-not-exception-Maybe
    ( f exception-Maybe)
    ( is-not-exception-injective-map-exception-Maybe is-inj-f x H)

value-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) → is-exception-Maybe (f (inl x)) → Y
value-injective-map-exception-Maybe {f = f} is-inj-f x H =
  value-is-value-Maybe
    ( f exception-Maybe)
    ( is-value-injective-map-exception-Maybe is-inj-f x H)

comp-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (H : is-exception-Maybe (f (inl x))) →
  Id ( inl (value-injective-map-exception-Maybe is-inj-f x H))
     ( f exception-Maybe)
comp-injective-map-exception-Maybe {f = f} is-inj-f x H =
  eq-is-value-Maybe
    ( f exception-Maybe)
    ( is-value-injective-map-exception-Maybe is-inj-f x H)

abstract
  is-not-exception-emb-exception-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ↪ Maybe Y)
    (x : X) → is-exception-Maybe (map-emb e (inl x)) →
    is-not-exception-Maybe (map-emb e exception-Maybe)
  is-not-exception-emb-exception-Maybe e =
    is-not-exception-injective-map-exception-Maybe (is-injective-emb e)

-- If e (inl x) is an exception, then e exception is a value
is-value-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) →
  is-value-Maybe (map-equiv e exception-Maybe)
is-value-map-equiv-exception-Maybe e x H =
  is-value-is-not-exception-Maybe
    ( map-equiv e exception-Maybe)
    ( is-not-exception-map-equiv-exception-Maybe e x H)

value-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) → Y
value-map-equiv-exception-Maybe e x H =
  value-is-value-Maybe
    ( map-equiv e exception-Maybe)
    ( is-value-map-equiv-exception-Maybe e x H)

comp-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (H : is-exception-Maybe (map-equiv e (inl x))) →
  Id ( inl (value-map-equiv-exception-Maybe e x H))
     ( map-equiv e exception-Maybe)
comp-map-equiv-exception-Maybe e x H =
  eq-is-value-Maybe
    ( map-equiv e exception-Maybe)
    ( is-value-map-equiv-exception-Maybe e x H)

-- Proposition 16.2.1 Step (ii) of the proof

restrict-injective-map-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) (u : Maybe Y) (p : Id (f (inl x)) u) → Y
restrict-injective-map-Maybe' {f = f} is-inj-f x (inl y) p = y
restrict-injective-map-Maybe' {f = f} is-inj-f x (inr star) p =
  value-injective-map-exception-Maybe is-inj-f x p

restrict-injective-map-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → X → Y
restrict-injective-map-Maybe {f = f} is-inj-f x =
  restrict-injective-map-Maybe' is-inj-f x (f (inl x)) refl

comp-restrict-injective-map-is-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (u : Maybe Y) (p : Id (f (inl x)) u) →
  is-exception-Maybe (f (inl x)) →
  Id (inl (restrict-injective-map-Maybe' is-inj-f x u p)) (f exception-Maybe)
comp-restrict-injective-map-is-exception-Maybe' {f = f} is-inj-f x (inl y) p q =
  ex-falso (is-not-exception-unit-Maybe y (inv p ∙ q))
comp-restrict-injective-map-is-exception-Maybe' {f = f} is-inj-f x (inr star) p q =
  comp-injective-map-exception-Maybe is-inj-f x p

comp-restrict-injective-map-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) → is-exception-Maybe (f (inl x)) →
  Id (inl (restrict-injective-map-Maybe is-inj-f x)) (f exception-Maybe)
comp-restrict-injective-map-is-exception-Maybe {f = f} is-inj-f x =
  comp-restrict-injective-map-is-exception-Maybe' is-inj-f x (f (inl x)) refl

comp-restrict-injective-map-is-not-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (u : Maybe Y) (p : Id (f (inl x)) u) →
  is-not-exception-Maybe (f (inl x)) →
  Id (inl (restrict-injective-map-Maybe' is-inj-f x u p)) (f (inl x))
comp-restrict-injective-map-is-not-exception-Maybe' is-inj-f x (inl y) p H =
  inv p
comp-restrict-injective-map-is-not-exception-Maybe' is-inj-f x (inr star) p H =
  ex-falso (H p)

comp-restrict-injective-map-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) → is-not-exception-Maybe (f (inl x)) →
  Id (inl (restrict-injective-map-Maybe is-inj-f x)) (f (inl x))
comp-restrict-injective-map-is-not-exception-Maybe {f = f} is-inj-f x =
  comp-restrict-injective-map-is-not-exception-Maybe' is-inj-f x (f (inl x))
    refl

-- An equivalence e : Maybe X ≃ Maybe Y induces a map X → Y. We don't use
-- with-abstraction to keep full control over the definitional equalities, so
-- we give the definition in two steps. After the definition is complete, we
-- also prove two computation rules. Since we will prove computation rules, we
-- make the definition abstract.

map-equiv-equiv-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y)
  (x : X) (u : Maybe Y) (p : Id (map-equiv e (inl x)) u) → Y
map-equiv-equiv-Maybe' e =
  restrict-injective-map-Maybe' (is-injective-map-equiv e)

map-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) → X → Y
map-equiv-equiv-Maybe e =
  restrict-injective-map-Maybe (is-injective-map-equiv e)

comp-map-equiv-equiv-is-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (u : Maybe Y) (p : Id (map-equiv e (inl x)) u) →
  is-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe' e x u p)) (map-equiv e exception-Maybe)
comp-map-equiv-equiv-is-exception-Maybe' e =
  comp-restrict-injective-map-is-exception-Maybe' (is-injective-map-equiv e)

comp-map-equiv-equiv-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe e x)) (map-equiv e exception-Maybe)
comp-map-equiv-equiv-is-exception-Maybe e x =
  comp-map-equiv-equiv-is-exception-Maybe' e x (map-equiv e (inl x)) refl

comp-map-equiv-equiv-is-not-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (u : Maybe Y) (p : Id (map-equiv e (inl x)) u) →
  is-not-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe' e x u p)) (map-equiv e (inl x))
comp-map-equiv-equiv-is-not-exception-Maybe' e x (inl y) p H =
  inv p
comp-map-equiv-equiv-is-not-exception-Maybe' e x (inr star) p H =
  ex-falso (H p)

comp-map-equiv-equiv-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-not-exception-Maybe (map-equiv e (inl x)) →
  Id (inl (map-equiv-equiv-Maybe e x)) (map-equiv e (inl x))
comp-map-equiv-equiv-is-not-exception-Maybe e x =
  comp-map-equiv-equiv-is-not-exception-Maybe' e x (map-equiv e (inl x)) refl

-- Proposition 16.2.1 Step (iii) of the proof

-- An equivalence e : Maybe X ≃ Maybe Y induces a map Y → X

map-inv-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) → Y → X
map-inv-equiv-equiv-Maybe e =
  map-equiv-equiv-Maybe (inv-equiv e)

comp-map-inv-equiv-equiv-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (y : Y) →
  is-exception-Maybe (map-inv-equiv e (inl y)) →
  Id (inl (map-inv-equiv-equiv-Maybe e y)) (map-inv-equiv e exception-Maybe)
comp-map-inv-equiv-equiv-is-exception-Maybe e =
  comp-map-equiv-equiv-is-exception-Maybe (inv-equiv e)

comp-map-inv-equiv-equiv-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (y : Y) →
  ( f : is-not-exception-Maybe (map-inv-equiv e (inl y))) →
  Id (inl (map-inv-equiv-equiv-Maybe e y)) (map-inv-equiv e (inl y))
comp-map-inv-equiv-equiv-is-not-exception-Maybe e =
  comp-map-equiv-equiv-is-not-exception-Maybe (inv-equiv e)

-- Proposition 16.2.1 Step (iv) of the proof
    
-- map-inv-equiv-equiv-Maybe e is a section of map-equiv-equiv-Maybe e.

abstract
  issec-map-inv-equiv-equiv-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
    (map-equiv-equiv-Maybe e ∘ map-inv-equiv-equiv-Maybe e) ~ id
  issec-map-inv-equiv-equiv-Maybe e y with
    is-decidable-is-exception-Maybe (map-inv-equiv e (inl y))
  ... | inl p =
    is-injective-unit-Maybe
      ( ( comp-map-equiv-equiv-is-exception-Maybe e
          ( map-inv-equiv-equiv-Maybe e y)
          ( ( ap
              ( map-equiv e)
              ( comp-map-inv-equiv-equiv-is-exception-Maybe e y p)) ∙
            ( issec-map-inv-equiv e exception-Maybe))) ∙
        ( ( ap (map-equiv e) (inv p)) ∙
          ( issec-map-inv-equiv e (inl y))))
  ... | inr f =
    is-injective-unit-Maybe
      ( ( comp-map-equiv-equiv-is-not-exception-Maybe e
          ( map-inv-equiv-equiv-Maybe e y)
          ( is-not-exception-is-value-Maybe
            ( map-equiv e (inl (map-inv-equiv-equiv-Maybe e y)))
            ( pair y
              ( inv
                ( ( ap
                    ( map-equiv e)
                    ( comp-map-inv-equiv-equiv-is-not-exception-Maybe e y f)) ∙
                  ( issec-map-inv-equiv e (inl y))))))) ∙
        ( ( ap
            ( map-equiv e)
            ( comp-map-inv-equiv-equiv-is-not-exception-Maybe e y f)) ∙
          ( issec-map-inv-equiv e (inl y))))

-- The map map-inv-equiv-equiv e is a retraction of the map map-equiv-equiv

abstract
  isretr-map-inv-equiv-equiv-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
    (map-inv-equiv-equiv-Maybe e ∘ map-equiv-equiv-Maybe e) ~ id
  isretr-map-inv-equiv-equiv-Maybe e x with
    is-decidable-is-exception-Maybe (map-equiv e (inl x))
  ... | inl p =
    is-injective-unit-Maybe
      ( ( comp-map-inv-equiv-equiv-is-exception-Maybe e
          ( map-equiv-equiv-Maybe e x)
          ( ( ap ( map-inv-equiv e)
                 ( comp-map-equiv-equiv-is-exception-Maybe e x p)) ∙
            ( isretr-map-inv-equiv e exception-Maybe))) ∙
        ( ( ap (map-inv-equiv e) (inv p)) ∙
          ( isretr-map-inv-equiv e (inl x))))
  ... | inr f =
    is-injective-unit-Maybe
      ( ( comp-map-inv-equiv-equiv-is-not-exception-Maybe e
          ( map-equiv-equiv-Maybe e x)
          ( is-not-exception-is-value-Maybe
            ( map-inv-equiv e (inl (map-equiv-equiv-Maybe e x)))
            ( pair x
              ( inv
                ( ( ap (map-inv-equiv e)
                       ( comp-map-equiv-equiv-is-not-exception-Maybe e x f)) ∙
                  ( isretr-map-inv-equiv e (inl x))))))) ∙
        ( ( ap ( map-inv-equiv e)
               ( comp-map-equiv-equiv-is-not-exception-Maybe e x f)) ∙
          ( isretr-map-inv-equiv e (inl x))))

-- Proposition 16.2.1 Conclusion of the proof

-- The function map-equiv-equiv-Maybe is an equivalence

abstract
  is-equiv-map-equiv-equiv-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
    is-equiv (map-equiv-equiv-Maybe e)
  is-equiv-map-equiv-equiv-Maybe e =
    is-equiv-has-inverse
      ( map-inv-equiv-equiv-Maybe e)
      ( issec-map-inv-equiv-equiv-Maybe e)
      ( isretr-map-inv-equiv-equiv-Maybe e)

equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (Maybe X ≃ Maybe Y) → (X ≃ Y)
pr1 (equiv-equiv-Maybe e) = map-equiv-equiv-Maybe e
pr2 (equiv-equiv-Maybe e) = is-equiv-map-equiv-equiv-Maybe e
```
