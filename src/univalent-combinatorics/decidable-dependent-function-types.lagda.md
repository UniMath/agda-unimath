# Decidable dependent function types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.decidable-dependent-function-types where

open import elementary-number-theory.decidable-dependent-function-types public

open import foundation.decidable-types using
  ( is-decidable; is-decidable-iff; is-decidable-Prop)
open import foundation.equivalences using (id-equiv)
open import foundation.functions using (map-Π)
open import foundation.global-choice using (elim-trunc-Prop-is-decidable)
open import foundation.propositional-truncations using
  ( type-trunc-Prop; map-universal-property-trunc-Prop; trunc-Prop;
    unit-trunc-Prop; apply-universal-property-trunc-Prop)
open import foundation.propositions using (Π-Prop)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.counting using
  ( count; equiv-count; map-equiv-count)
open import univalent-combinatorics.finite-choice using (finite-choice)
open import univalent-combinatorics.finite-types using (is-finite)
```

## Idea

We describe conditions under which dependent products are decidable.

```agda
is-decidable-Π-count :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → is-decidable (B x)) → is-decidable ((x : A) → B x)
is-decidable-Π-count e d =
  is-decidable-Π-equiv
    ( equiv-count e)
    ( λ x → id-equiv)
    ( is-decidable-Π-Fin (λ x → d (map-equiv-count e x)))

is-decidable-Π-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-finite A →
  ((x : A) → is-decidable (B x)) → is-decidable ((x : A) → B x)
is-decidable-Π-is-finite {l1} {l2} {A} {B} H d =
  is-decidable-iff
    ( map-Π (λ x → elim-trunc-Prop-is-decidable (d x)))
    ( map-Π (λ x → unit-trunc-Prop))
    ( is-decidable-iff
      ( α)
      ( finite-choice H)
      ( apply-universal-property-trunc-Prop H
        ( is-decidable-Prop (trunc-Prop ((x : A) → B x)))
        ( λ e →
          is-decidable-iff
            ( finite-choice H)
            ( α)
            ( is-decidable-Π-count e
              ( λ x →
                is-decidable-iff
                  ( unit-trunc-Prop)
                  ( elim-trunc-Prop-is-decidable (d x))
                  ( d x))))))
  where
  α : type-trunc-Prop ((x : A) → B x) → (x : A) → type-trunc-Prop (B x)
  α = map-universal-property-trunc-Prop
        ( Π-Prop A (λ x → trunc-Prop (B x)))
        ( λ (f : (x : A) → B x) (x : A) → unit-trunc-Prop (f x))
```
