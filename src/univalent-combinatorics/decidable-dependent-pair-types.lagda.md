# Decidability of dependent pair types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.decidable-dependent-pair-types where

open import foundation.decidable-dependent-pair-types public

open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (id-equiv)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.counting using (count; equiv-count)
```

## Idea

We describe conditions under which dependent sums are decidable. Note that it is _not_ the case for a family `B` of decidable types over a finite type `A`, that the dependent pair type `Σ A B` is decidable.

```agda
is-decidable-Σ-count :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count A →
  ((x : A) → is-decidable (B x)) → is-decidable (Σ A B)
is-decidable-Σ-count e d =
  is-decidable-Σ-equiv
    ( equiv-count e)
    ( λ x → id-equiv)
    ( is-decidable-Σ-Fin (λ x → d (map-equiv-count e x)))
```
