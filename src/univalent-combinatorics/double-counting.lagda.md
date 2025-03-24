# Double counting

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module univalent-combinatorics.double-counting
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.identity-types funext
open import foundation.universe-levels

open import univalent-combinatorics.counting funext univalence truncations
open import univalent-combinatorics.standard-finite-types funext univalence truncations
```

</details>

## Idea

Given two countings of the same type, we obtain the same number of its elements.
Likewise, given two countings of equivalent types, we obtain the same number of
their elements.

```agda
abstract
  double-counting-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-A : count A)
    (count-B : count B) (e : A ≃ B) →
    Id (number-of-elements-count count-A) (number-of-elements-count count-B)
  double-counting-equiv (k , f) (l , g) e =
    is-equivalence-injective-Fin (inv-equiv g ∘e e ∘e f)

abstract
  double-counting :
    {l : Level} {A : UU l} (count-A count-A' : count A) →
    Id (number-of-elements-count count-A) (number-of-elements-count count-A')
  double-counting count-A count-A' =
    double-counting-equiv count-A count-A' id-equiv
```
