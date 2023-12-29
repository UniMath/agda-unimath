# My file about computing `htpy-precomp`

```agda
module foundation.my-file-about-computing-htpy-precomp where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.homotopies
open import foundation-core.whiskering-homotopies
```

</details>

## Properties

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f g : A → B}
  where

  compute-htpy-precomp-right-whisker :
    (h : C → A) (H : f ~ g) (S : UU l4) →
    precomp h S ·l htpy-precomp H S ~ htpy-precomp (H ·r h) S
  compute-htpy-precomp-right-whisker h H S i =
    coherence-square-eq-htpy-ap-precomp h (i ∘ f) (i ∘ g) (i ·l H)

  compute-htpy-precomp-left-whisker :
    (h : B → C) (H : f ~ g) (S : UU l4) →
    htpy-precomp H S ·r precomp h S ~ htpy-precomp (h ·l H) S
  compute-htpy-precomp-left-whisker h H S i =
    ap eq-htpy (eq-htpy (ap-comp i h ∘ H))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {f g h : A → B}
  where

  distributive-htpy-precomp-concat-htpy :
    (H : f ~ g) (K : g ~ h) (S : UU l3) →
    htpy-precomp (H ∙h K) S ~ htpy-precomp H S ∙h htpy-precomp K S
  distributive-htpy-precomp-concat-htpy H K S i =
    ( ap eq-htpy (eq-htpy (distributive-left-whisk-concat-htpy i H K))) ∙
    ( eq-htpy-concat-htpy (i ·l H) (i ·l K))
```
