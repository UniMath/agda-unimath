# Epimorphisms of sets

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.epimorphisms-with-respect-to-sets where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb)
open import foundation.equivalences using (map-equiv)
open import foundation.existential-quantification using (∃-Prop)
open import foundation.function-extensionality using
  ( eq-htpy; htpy-eq; funext)
open import foundation.functions using (precomp; _∘_)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (inv; ap; _∙_; Id; refl)
open import foundation.injective-maps using
  ( is-emb-is-injective; is-injective-is-emb)
open import foundation.propositional-extensionality using
  ( eq-iff; UU-Prop-Set)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; unit-trunc-Prop)
open import foundation.propositions using (UU-Prop)
open import foundation.sets using
  ( UU-Set; type-Set; is-set-type-Set; is-set-function-type; Id-Prop;
    precomp-Set)
open import foundation.surjective-maps using (is-surjective)
open import foundation.unit-type using (raise-unit-Prop; raise-star)
open import foundation.univalence using (equiv-eq)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)
```

## Idea

An epimorphism with respect to maps into sets are maps `f : A → B` suc that for every set `C` the precomposition function `(B → C) → (A → C)` is an embedding.

## Definition

```agda
is-epimorphism-Set :
  {l1 l2 : Level} (l : Level) {A : UU l1} {B : UU l2}
  (f : A → B) → UU (l1 ⊔ l2 ⊔ lsuc l)
is-epimorphism-Set l f =
  (C : UU-Set l) → is-emb (precomp-Set f C)
```

## Properties

### Surjective maps are epimorphisms with respect to maps into sets

```agda
abstract
  is-epimorphism-is-surjective-Set :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-surjective f → {l : Level} → is-epimorphism-Set l f
  is-epimorphism-is-surjective-Set H C =
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
```

### Maps that are epimorphisms with respect to maps into sets are surjective

```agda
abstract
  is-surjective-is-epimorphism-Set :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    ({l : Level} → is-epimorphism-Set l f) → is-surjective f
  is-surjective-is-epimorphism-Set {l1} {l2} {A} {B} {f} H b =
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
```
