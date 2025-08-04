# The action on binary homotopies

```agda
module foundation.action-on-binary-homotopies-binary-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.homotopy-induction
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Definition

```agda
ap-binary-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f g : A → B} (H : f ~ g) (m : B → B → C)
  {x y : A} →
  ap-binary m (H x) (H y) ＝ ap (λ f → m (f x) (f y)) (eq-htpy H)
ap-binary-htpy {f = f} H m {x = x} {y = y} =
  ind-htpy f
    ( λ g H → ap-binary m (H x) (H y) ＝ ap (λ f → m (f x) (f y)) (eq-htpy H))
    ( inv
      (ap (ap (λ f → m (f x) (f y))) (eq-htpy-refl-htpy _)))
    ( H)

```
