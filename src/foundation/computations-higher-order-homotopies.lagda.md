# Computations with higher-order homotopies

```agda
module foundation.computations-higher-order-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.function-extensionality
open import foundation.homotopy-induction
open import foundation.path-algebra
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Computations

### Commutativity between whiskering with `precomp` and `postcomp` homotopies

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  commutative-postcomp-htpy-precomp :
    {f f' : A → B} (g : X → Y) (F : f ~ f') →
    htpy-precomp F Y ·r postcomp B g ~ postcomp A g ·l htpy-precomp F X
  commutative-postcomp-htpy-precomp {f} g =
    ind-htpy f
      ( λ f' F →
        htpy-precomp F Y ·r postcomp B g ~ postcomp A g ·l htpy-precomp F X)
      ( ( ap-right-whisk-htpy
          ( compute-htpy-precomp-refl-htpy f Y)
          ( postcomp B g)) ∙h
        ( inv-htpy
          ( ap-left-whisk-htpy
            ( postcomp A g)
            ( compute-htpy-precomp-refl-htpy f X))))

  commutative-precomp-htpy-postcomp :
    (f : A → B) {g g' : X → Y} (G : g ~ g') →
    htpy-postcomp A G ·r precomp f X ~ precomp f Y ·l htpy-postcomp B G
  commutative-precomp-htpy-postcomp f {g} =
    ind-htpy g
      ( λ g' G →
        htpy-postcomp A G ·r precomp f X ~ precomp f Y ·l htpy-postcomp B G)
      ( ( ap-right-whisk-htpy
          ( compute-htpy-postcomp-refl-htpy A g)
          ( precomp f X)) ∙h
        ( inv-htpy
          ( ap-left-whisk-htpy
            ( precomp f Y)
            ( compute-htpy-postcomp-refl-htpy B g))))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f f' : A → B} {g g' : X → Y}
  where

  commutative-htpy-postcomp-htpy-precomp :
    (F : f ~ f') (G : g ~ g') →
    ( postcomp A g ·l htpy-precomp F X ∙h htpy-postcomp A G ·r precomp f' X) ~
    ( precomp f Y ·l htpy-postcomp B G ∙h htpy-precomp F Y ·r postcomp B g')
  commutative-htpy-postcomp-htpy-precomp F =
    ind-htpy
      ( g)
      ( λ g' G →
        ( postcomp A g ·l htpy-precomp F X ∙h
          htpy-postcomp A G ·r precomp f' X) ~
        ( precomp f Y ·l htpy-postcomp B G ∙h
          htpy-precomp F Y ·r postcomp B g'))
      ( ( ap-concat-htpy
          ( postcomp A g ·l htpy-precomp F X)
          ( ap-right-whisk-htpy
            ( compute-htpy-postcomp-refl-htpy A g)
            ( precomp f' X))) ∙h
        ( right-unit-htpy) ∙h
        ( inv-htpy (commutative-postcomp-htpy-precomp g F)) ∙h
        ( ap-concat-htpy'
          ( htpy-precomp F Y ·r postcomp B g)
          ( ap-left-whisk-htpy
            ( precomp f Y)
            ( inv-htpy (compute-htpy-postcomp-refl-htpy B g)))))
```
