# The univalence axiom implies function extensionality

```agda
module foundation.univalence-implies-function-extensionality where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalence-induction
open import foundation.function-extensionality
open import foundation.postcomposition-functions
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.weak-function-extensionality

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retracts-of-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

The [univalence axiom](foundation-core.univalence.md) implies
[function extensionality](foundation.function-extensionality.md).

## Theorem

```agda
retract-compute-fiber-id-postcomp-pr1 :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((a : A) → B a) retract-of (fiber (postcomp A (pr1 {B = B})) id)
retract-compute-fiber-id-postcomp-pr1 {B = B} =
  ( λ f → ((λ x → (x , f x)) , refl)) ,
  ( λ h x → tr B (htpy-eq (pr2 h) x) (pr2 (pr1 h x))) ,
  ( refl-htpy)

abstract
  weak-funext-univalence : {l : Level} → weak-function-extensionality-Level l l
  weak-funext-univalence A B is-contr-B =
    is-contr-retract-of
      ( fiber (postcomp A pr1) id)
      ( retract-compute-fiber-id-postcomp-pr1)
      ( is-contr-map-is-equiv
        ( is-equiv-postcomp-univalence A (equiv-pr1 is-contr-B))
        ( id))

abstract
  funext-univalence :
    {l : Level} → function-extensionality-Level l l
  funext-univalence f = funext-weak-funext weak-funext-univalence f
```
