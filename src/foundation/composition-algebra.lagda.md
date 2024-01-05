# Composition algebra

```agda
module foundation.composition-algebra where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopy-induction
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

## Idea

This file collects various interactions of
[pre-](foundation-core.precomposition-functions.md) and
[postcomposition](foundation-core.postcomposition-functions.md) with
[homotopies](foundation-core.homotopies.md).

Given a [homotopy of maps](foundation-core.homotopies.md) `H : f ~ g`, we have
witnesses

```text
  htpy-precomp H S : precomp f S ~ precomp g S
```

and

```text
  htpy-postcomp S H : postcomp S f ~ postcomp S g
```

This file records their interactions with different operations on homotopies and
eachother.

## Properties

### Precomposition distributes over whiskerings and concatenations of homotopies

The operation `htpy-precomp` distributes over whiskerings contravariantly:

```text
    precomp h S ·l htpy-precomp H S ~ htpy-precomp (H ·r h) S
```

and

```text
  htpy-precomp H S ·r precomp h S ~ htpy-precomp (h ·l H) S.
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f g : A → B}
  where

  distributive-htpy-precomp-right-whisker :
    (h : C → A) (H : f ~ g) (S : UU l4) →
    precomp h S ·l htpy-precomp H S ~ htpy-precomp (H ·r h) S
  distributive-htpy-precomp-right-whisker h H S i =
    coherence-square-eq-htpy-ap-precomp h (i ∘ f) (i ∘ g) (i ·l H)

  distributive-htpy-precomp-left-whisker :
    (h : B → C) (H : f ~ g) (S : UU l4) →
    htpy-precomp H S ·r precomp h S ~ htpy-precomp (h ·l H) S
  distributive-htpy-precomp-left-whisker h H S i =
    ap eq-htpy (eq-htpy (ap-comp i h ∘ H))
```

The operation `htpy-precomp` distributes over concatenation of homotopies:

```text
  htpy-precomp (H ∙h K) S ~ htpy-precomp H S ∙h htpy-precomp K Ss
```

```agda
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

### Postcomposition distributes over whiskerings and concatenations of homotopies

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f g : A → B}
  where

  distributive-htpy-postcomp-right-whisker :
    (h : C → A) (H : f ~ g) (S : UU l4) →
    htpy-postcomp S H ·r postcomp S h ~ htpy-postcomp S (H ·r h)
  distributive-htpy-postcomp-right-whisker h H S = refl-htpy

  distributive-htpy-postcomp-left-whisker :
    (h : B → C) (H : f ~ g) (S : UU l4) →
    postcomp S h ·l htpy-postcomp S H ~ htpy-postcomp S (h ·l H)
  distributive-htpy-postcomp-left-whisker h H S i =
    coherence-square-eq-htpy-ap-postcomp h (f ∘ i) (g ∘ i) (H ·r i)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {f g h : A → B}
  where

  distributive-htpy-postcomp-concat-htpy :
    (H : f ~ g) (K : g ~ h) (S : UU l3) →
    htpy-postcomp S (H ∙h K) ~ htpy-postcomp S H ∙h htpy-postcomp S K
  distributive-htpy-postcomp-concat-htpy H K S i =
    ( ap eq-htpy (eq-htpy (distributive-right-whisk-concat-htpy i H K))) ∙
    ( eq-htpy-concat-htpy (H ·r i) (K ·r i))
```

### The actions of precomposition and postcomposition on homotopies commute

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

## See also

- [Path algebra](foundation.path-algebra.md)
