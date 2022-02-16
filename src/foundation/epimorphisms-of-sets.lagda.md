# Epimorphisms of sets

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.epimorphisms-of-sets where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb)
open import foundation.equivalences using
  ( map-equiv; is-equiv-top-is-equiv-bottom-square)
open import foundation.existential-quantification using (∃-Prop)
open import foundation.function-extensionality using
  ( eq-htpy; htpy-eq; funext)
open import foundation.functions using (precomp; _∘_)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (inv; ap; _∙_; Id; refl)
open import foundation.injective-maps using
  ( is-emb-is-injective; is-injective-is-emb)
open import foundation.propositional-extensionality using (eq-iff)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; unit-trunc-Prop)
open import foundation.propositions using (UU-Prop)
open import foundation.sets using
  ( UU-Set; type-Set; is-set-type-Set; is-set-function-type; Id-Prop)
open import foundation.subuniverses using (UU-Prop-Set)
open import foundation.surjective-maps using
  ( is-surjective; dependent-universal-property-surj-is-surjective)
open import foundation.unit-type using (raise-unit-Prop; raise-star)
open import foundation.univalence using (equiv-eq)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

An epimorphism between sets is a map `f : A → B` between sets such that precomposition by `f` is an embedding.

## Properties

```agda
precomp-Set :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : UU-Set l3) →
  (B → type-Set C) → (A → type-Set C)
precomp-Set f C = precomp f (type-Set C)

abstract
  is-emb-precomp-Set-is-surjective :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-surjective f → (C : UU-Set l3) → is-emb (precomp-Set f C)
  is-emb-precomp-Set-is-surjective H C =
    is-emb-is-injective
      ( is-set-function-type (is-set-type-Set C))
      ( λ {g} {h} p →
        eq-htpy (λ b →
          apply-universal-property-trunc-Prop
            ( H b)
            ( Id-Prop C (g b) (h b))
            ( λ u →
              ( inv (ap g (pr2 u))) ∙
              ( ( htpy-eq p (pr1 u))  ∙
                ( ap h (pr2 u))))))

abstract
  is-surjective-is-emb-precomp-Set :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    ({l3 : Level} (C : UU-Set l3) → is-emb (precomp-Set f C)) → is-surjective f
  is-surjective-is-emb-precomp-Set {l1} {l2} {A} {B} {f} H b =
    map-equiv
      ( equiv-eq
        ( ap ( pr1)
             ( htpy-eq
               ( is-injective-is-emb
                 ( H (UU-Prop-Set (l1 ⊔ l2)))
                 { g}
                 { h}
                 ( eq-htpy
                   ( λ a →
                     eq-iff
                       ( λ _ → unit-trunc-Prop (pair a refl))
                       ( λ _ → raise-star))))
               ( b))))
      ( raise-star)
    where
    g : B → UU-Prop (l1 ⊔ l2)
    g y = raise-unit-Prop (l1 ⊔ l2)
    h : B → UU-Prop (l1 ⊔ l2)
    h y = ∃-Prop (λ x → Id (f x) y)

-- Exercise 17.11

square-htpy-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B) →
  ( g h : B → C) →
  ( (λ (p : (y : B) → Id (g y) (h y)) (x : A) → p (f x)) ∘ htpy-eq) ~
  ( htpy-eq ∘ (ap (precomp f C)))
square-htpy-eq f g .g refl = refl

abstract
  is-emb-precomp-is-surjective :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-surjective f → (C : UU-Set l3) → is-emb (precomp f (type-Set C))
  is-emb-precomp-is-surjective {f = f} is-surj-f C g h =
    is-equiv-top-is-equiv-bottom-square
      ( htpy-eq)
      ( htpy-eq)
      ( ap (precomp f (type-Set C)))
      ( λ p a → p (f a))
      ( square-htpy-eq f g h)
      ( funext g h)
      ( funext (g ∘ f) (h ∘ f))
      ( dependent-universal-property-surj-is-surjective f is-surj-f
        ( λ a → Id-Prop C (g a) (h a)))
```
