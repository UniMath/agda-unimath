# Equivalence induction

```agda
module foundation.equivalence-induction where

open import foundation-core.equivalence-induction public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.sections
```

</details>

## Idea

Equivalence induction is a condition equivalent to the univalence axiom

## Theorem

```agda
abstract
  Ind-equiv :
    {l1 l2 : Level} (A : UU l1) (P : (B : UU l1) (e : A ≃ B) → UU l2) →
    section (ev-id P)
  Ind-equiv A P =
    IND-EQUIV-is-contr-total-equiv
    ( is-contr-total-equiv A)
    ( λ t → P (pr1 t) (pr2 t))

ind-equiv :
  {l1 l2 : Level} (A : UU l1) (P : (B : UU l1) (e : A ≃ B) → UU l2) →
  P A id-equiv → {B : UU l1} (e : A ≃ B) → P B e
ind-equiv A P p {B} = pr1 (Ind-equiv A P) p B
```

## Corollaries

### Equivalence induction implies that postcomposing by an equivalence is an equivalence

Of course we already know this fact from function extensionality, but we prove
it again from equivalence induction so that we can prove that univalence implies
function extensionality.

```agda
abstract
  is-equiv-postcomp-univalence :
    {l1 l2 : Level} {X Y : UU l1} (A : UU l2) (e : X ≃ Y) →
    is-equiv (postcomp A (map-equiv e))
  is-equiv-postcomp-univalence {X = X} A =
    ind-equiv X (λ Y e → is-equiv (postcomp A (map-equiv e))) is-equiv-id
```
