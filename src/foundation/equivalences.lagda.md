# Equivalences

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.equivalences where

open import foundation-core.equivalences public

open import foundation-core.commuting-squares using (coherence-square)
open import foundation-core.contractible-maps using (is-contr-map-is-equiv)
open import foundation-core.contractible-types using (is-contr-equiv)
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.embeddings using (is-emb; _↪_)
open import foundation-core.fibers-of-maps using (fib)
open import foundation-core.functoriality-dependent-pair-types using (equiv-tot)
open import foundation-core.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)

open import foundation.identity-types using
  ( Id; refl; equiv-inv; ap; equiv-concat'; inv; _∙_; concat'; assoc; concat;
    left-inv; right-unit; distributive-inv-concat; con-inv; inv-inv; ap-inv)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

An equivalence is a map that has a section and a (separate) retraction. This may look odd: Why not say that an equivalence is a map that has a 2-sided inverse? The reason is that the latter requirement would put nontrivial structure on the map, whereas having the section and retraction separate yields a property. To quickly see this: if `f` is an equivalence, then it has up to homotopy only one section, and it has up to homotopy only one retraction. 

## Properties

### Any equivalence is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-emb-is-equiv : {f : A → B} → is-equiv f → is-emb f
  is-emb-is-equiv {f} is-equiv-f x =
    fundamental-theorem-id x refl
      ( is-contr-equiv
        ( fib f (f x))
        ( equiv-tot (λ y → equiv-inv (f x) (f y)))
        ( is-contr-map-is-equiv is-equiv-f (f x)))
      ( λ y p → ap f p)

  emb-equiv : (A ≃ B) → (A ↪ B)
  pr1 (emb-equiv e) = map-equiv e
  pr2 (emb-equiv e) = is-emb-is-equiv (is-equiv-map-equiv e)

  equiv-ap :
    (e : A ≃ B) (x y : A) → (Id x y) ≃ (Id (map-equiv e x) (map-equiv e y))
  pr1 (equiv-ap e x y) = ap (map-equiv e) {x} {y}
  pr2 (equiv-ap e x y) = is-emb-is-equiv (is-equiv-map-equiv e) x y
```

### Transposing equalities along equivalences

The fact that equivalences are embeddings has many important consequences, we will use some of these consequences in order to derive basic properties of embeddings.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  eq-transpose-equiv :
    (x : A) (y : B) → (Id (map-equiv e x) y) ≃ (Id x (map-inv-equiv e y))
  eq-transpose-equiv x y =
    ( inv-equiv (equiv-ap e x (map-inv-equiv e y))) ∘e
    ( equiv-concat'
      ( map-equiv e x)
      ( inv (issec-map-inv-equiv e y)))

  map-eq-transpose-equiv :
    {x : A} {y : B} → Id (map-equiv e x) y → Id x (map-inv-equiv e y)
  map-eq-transpose-equiv {x} {y} = map-equiv (eq-transpose-equiv x y)

  inv-map-eq-transpose-equiv :
    {x : A} {y : B} → Id x (map-inv-equiv e y) → Id (map-equiv e x) y
  inv-map-eq-transpose-equiv {x} {y} = map-inv-equiv (eq-transpose-equiv x y)

  triangle-eq-transpose-equiv :
    {x : A} {y : B} (p : Id (map-equiv e x) y) →
    Id ( ( ap (map-equiv e) (map-eq-transpose-equiv p)) ∙
         ( issec-map-inv-equiv e y))
       ( p)
  triangle-eq-transpose-equiv {x} {y} p =
    ( ap ( concat' (map-equiv e x) (issec-map-inv-equiv e y))
         ( issec-map-inv-equiv
           ( equiv-ap e x (map-inv-equiv e y))
           ( p ∙ inv (issec-map-inv-equiv e y)))) ∙
    ( ( assoc p (inv (issec-map-inv-equiv e y)) (issec-map-inv-equiv e y)) ∙
      ( ( ap (concat p y) (left-inv (issec-map-inv-equiv e y))) ∙ right-unit))
  
  map-eq-transpose-equiv' :
    {a : A} {b : B} → Id b (map-equiv e a) → Id (map-inv-equiv e b) a
  map-eq-transpose-equiv' p = inv (map-eq-transpose-equiv (inv p))

  inv-map-eq-transpose-equiv' :
    {a : A} {b : B} → Id (map-inv-equiv e b) a → Id b (map-equiv e a)
  inv-map-eq-transpose-equiv' p =
    inv (inv-map-eq-transpose-equiv (inv p))

  triangle-eq-transpose-equiv' :
    {x : A} {y : B} (p : Id y (map-equiv e x)) →
    Id ( (issec-map-inv-equiv e y) ∙ p)
      ( ap (map-equiv e) (map-eq-transpose-equiv' p))
  triangle-eq-transpose-equiv' {x} {y} p =
    map-inv-equiv
      ( equiv-ap
        ( equiv-inv (map-equiv e (map-inv-equiv e y)) (map-equiv e x))
        ( (issec-map-inv-equiv e y) ∙ p)
        ( ap (map-equiv e) (map-eq-transpose-equiv' p)))
      ( ( distributive-inv-concat (issec-map-inv-equiv e y) p) ∙
        ( ( inv
            ( con-inv
              ( ap (map-equiv e) (inv (map-eq-transpose-equiv' p)))
              ( issec-map-inv-equiv e y)
              ( inv p)
              ( ( ap ( concat' (map-equiv e x) (issec-map-inv-equiv e y))
                     ( ap ( ap (map-equiv e))
                          ( inv-inv
                            ( map-inv-equiv
                              ( equiv-ap e x (map-inv-equiv e y))
                              ( ( inv p) ∙
                                ( inv (issec-map-inv-equiv e y))))))) ∙
                ( triangle-eq-transpose-equiv (inv p))))) ∙
          ( ap-inv (map-equiv e) (map-eq-transpose-equiv' p))))
```
