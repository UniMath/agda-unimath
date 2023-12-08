# My file about computing `htpy-precomp`

```agda
module foundation.my-file-about-computing-htpy-precomp where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.precomposition-functions
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.homotopies
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

```agda
compute-htpy-precomp-right-whisker :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f g : A → B} (h : C → A) (H : f ~ g) (S : UU l4) →
  precomp h S ·l htpy-precomp H S ~ htpy-precomp (H ·r h) S
compute-htpy-precomp-right-whisker {f = f} {g} h H S i =
  coherence-square-eq-htpy-ap-precomp h (i ∘ f) (i ∘ g) (i ·l H)

compute-htpy-precomp-left-whisker :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f g : A → B} (h : B → C) (H : f ~ g) (S : UU l4) →
  htpy-precomp H S ·r precomp h S ~ htpy-precomp (h ·l H) S
compute-htpy-precomp-left-whisker {f = f} {g} h H S i =
  ap eq-htpy (eq-htpy (ap-comp i h ∘ H))
```
