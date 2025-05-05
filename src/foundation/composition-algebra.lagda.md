# Composition algebra

```agda
module foundation.composition-algebra where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.function-extensionality
open import foundation.homotopy-induction
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.universe-levels
open import foundation.whiskering-higher-homotopies-composition
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

Given a [homotopy of maps](foundation-core.homotopies.md) `H : f ~ g`, there are
standard witnesses

```text
  htpy-precomp H S : precomp f S ~ precomp g S
```

and

```text
  htpy-postcomp S H : postcomp S f ~ postcomp S g.
```

This file records their interactions with each other and different operations on
homotopies.

## Properties

### Precomposition distributes over whiskerings of homotopies

The operation `htpy-precomp` distributes over
[whiskerings of homotopies](foundation.whiskering-homotopies-composition.md)
contravariantly. Given a homotopy `H : f ~ g` and a suitable map `h` the
homotopy constructed as the whiskering

```text
               - ∘ f
          ----------------->         - ∘ h
  (B → S)  htpy-precomp H S  (A → S) -----> (C → S)
          ----------------->
               - ∘ g
```

is homotopic to the homotopy

```text
                    - ∘ (f ∘ h)
            -------------------------->
    (B → S)   htpy-precomp (H ·r h) S   (C → S).
            -------------------------->
                    - ∘ (g ∘ h)
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f g : A → B}
  where

  inv-distributive-htpy-precomp-right-whisker :
    (h : C → A) (H : f ~ g) (S : UU l4) →
    precomp h S ·l htpy-precomp H S ~ htpy-precomp (H ·r h) S
  inv-distributive-htpy-precomp-right-whisker h H S i =
    coherence-eq-htpy-ap-precomp h (i ·l H)

  distributive-htpy-precomp-right-whisker :
    (h : C → A) (H : f ~ g) (S : UU l4) →
    htpy-precomp (H ·r h) S ~ precomp h S ·l htpy-precomp H S
  distributive-htpy-precomp-right-whisker h H S =
    inv-htpy (inv-distributive-htpy-precomp-right-whisker h H S)
```

Similarly, the homotopy given by the whiskering

```text
                               - ∘ f
          - ∘ h          ----------------->
  (C → S) -----> (B → S)  htpy-precomp H S  (A → S)
                         ----------------->
                               - ∘ g
```

is homotopic to the homotopy

```text
                    - ∘ (h ∘ f)
            -------------------------->
    (C → S)   htpy-precomp (h · l H) S   (A → S).
            -------------------------->
                    - ∘ (h ∘ g)
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f g : A → B}
  where

  inv-distributive-htpy-precomp-left-whisker :
    (h : B → C) (H : f ~ g) (S : UU l4) →
    htpy-precomp H S ·r precomp h S ~ htpy-precomp (h ·l H) S
  inv-distributive-htpy-precomp-left-whisker h H S i =
    ap eq-htpy (eq-htpy (ap-comp i h ∘ H))

  distributive-htpy-precomp-left-whisker :
    (h : B → C) (H : f ~ g) (S : UU l4) →
    htpy-precomp (h ·l H) S ~ htpy-precomp H S ·r precomp h S
  distributive-htpy-precomp-left-whisker h H S =
    inv-htpy (inv-distributive-htpy-precomp-left-whisker h H S)
```

### Precomposition distributes over concatenations of homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {f g h : A → B}
  where

  distributive-htpy-precomp-concat-htpy :
    (H : f ~ g) (K : g ~ h) (S : UU l3) →
    htpy-precomp (H ∙h K) S ~ htpy-precomp H S ∙h htpy-precomp K S
  distributive-htpy-precomp-concat-htpy H K S i =
    ( ap eq-htpy (eq-htpy (distributive-left-whisker-comp-concat i H K))) ∙
    ( eq-htpy-concat-htpy (i ·l H) (i ·l K))
```

### Postcomposition distributes over whiskerings of homotopies

Given a homotopy `H : f ~ g` and a suitable map `h` the homotopy given by the
whiskering

```text
                               f ∘ –
          h ∘ -          ------------------>
  (S → C) -----> (S → B)  htpy-postcomp S H  (S → A)
                         ------------------>
                               g ∘ -
```

is homotopic to the homotopy

```text
                    (f ∘ h) ∘ -
            -------------------------->
    (S → C)   htpy-postcomp S (H ·r h)   (S → A).
            -------------------------->
                    (g ∘ h) ∘ -
```

In fact, they are syntactically equal.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f g : A → B}
  where

  inv-distributive-htpy-postcomp-right-whisker :
    (h : C → A) (H : f ~ g) (S : UU l4) →
    htpy-postcomp S (H ·r h) ~ htpy-postcomp S H ·r postcomp S h
  inv-distributive-htpy-postcomp-right-whisker h H S = refl-htpy

  distributive-htpy-postcomp-right-whisker :
    (h : C → A) (H : f ~ g) (S : UU l4) →
    htpy-postcomp S H ·r postcomp S h ~ htpy-postcomp S (H ·r h)
  distributive-htpy-postcomp-right-whisker h H S = refl-htpy
```

Similarly, the homotopy given by the whiskering

```text
                f ∘ -
          ----------------->          h ∘ -
  (S → A)  htpy-postcomp S H  (S → B) -----> (S → C)
          ----------------->
                g ∘ -
```

is homotopic to the homotopy

```text
                    (h ∘ f) ∘ -
            -------------------------->
    (S → A)   htpy-postcomp S (h ·l H)   (S → C).
            -------------------------->
                    (h ∘ g) ∘ -
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f g : A → B}
  where

  inv-distributive-htpy-postcomp-left-whisker :
    (h : B → C) (H : f ~ g) (S : UU l4) →
    postcomp S h ·l htpy-postcomp S H ~ htpy-postcomp S (h ·l H)
  inv-distributive-htpy-postcomp-left-whisker h H S i =
    compute-eq-htpy-ap-postcomp h (H ·r i)

  distributive-htpy-postcomp-left-whisker :
    (h : B → C) (H : f ~ g) (S : UU l4) →
    htpy-postcomp S (h ·l H) ~ postcomp S h ·l htpy-postcomp S H
  distributive-htpy-postcomp-left-whisker h H S =
    inv-htpy (inv-distributive-htpy-postcomp-left-whisker h H S)
```

### Postcomposition distributes over concatenations of homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {f g h : A → B}
  where

  distributive-htpy-postcomp-concat-htpy :
    (H : f ~ g) (K : g ~ h) (S : UU l3) →
    htpy-postcomp S (H ∙h K) ~ htpy-postcomp S H ∙h htpy-postcomp S K
  distributive-htpy-postcomp-concat-htpy H K S i =
    ( ap eq-htpy (eq-htpy (distributive-right-whisker-comp-concat i H K))) ∙
    ( eq-htpy-concat-htpy (H ·r i) (K ·r i))
```

### The actions of precomposition and postcomposition on homotopies commute

Given homotopies `F : f ~ f'` and `G : g ~ g'`, we have a commuting square of
homotopies

```text
                        postcomp A g ·l htpy-precomp F X
           (g ∘ - ∘ f) ---------------------------------> (g ∘ - ∘ f')
                |                                              |
                |                                              |
                |                                              |
  precomp f Y ·l htpy-postcomp B G            htpy-postcomp A G ·r precomp f' X
                |                                              |
                |                                              |
                ∨                                              ∨
          (g' ∘ - ∘ f) --------------------------------> (g' ∘ - ∘ f').
                       htpy-precomp F Y ·r postcomp B g'
```

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
      ( ( right-whisker-comp²
          ( compute-htpy-precomp-refl-htpy f Y)
          ( postcomp B g)) ∙h
        ( inv-htpy
          ( left-whisker-comp²
            ( postcomp A g)
            ( compute-htpy-precomp-refl-htpy f X))))

  commutative-precomp-htpy-postcomp :
    (f : A → B) {g g' : X → Y} (G : g ~ g') →
    htpy-postcomp A G ·r precomp f X ~ precomp f Y ·l htpy-postcomp B G
  commutative-precomp-htpy-postcomp f {g} =
    ind-htpy g
      ( λ g' G →
        htpy-postcomp A G ·r precomp f X ~ precomp f Y ·l htpy-postcomp B G)
      ( ( right-whisker-comp²
          ( compute-htpy-postcomp-refl-htpy A g)
          ( precomp f X)) ∙h
        ( inv-htpy
          ( left-whisker-comp²
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
    ind-htpy g
      ( λ g' G →
        ( postcomp A g ·l htpy-precomp F X ∙h
          htpy-postcomp A G ·r precomp f' X) ~
        ( precomp f Y ·l htpy-postcomp B G ∙h
          htpy-precomp F Y ·r postcomp B g'))
      ( ( ap-concat-htpy
          ( postcomp A g ·l htpy-precomp F X)
          ( right-whisker-comp²
            ( compute-htpy-postcomp-refl-htpy A g)
            ( precomp f' X))) ∙h
        ( right-unit-htpy) ∙h
        ( inv-htpy (commutative-postcomp-htpy-precomp g F)) ∙h
        ( ap-concat-htpy'
          ( htpy-precomp F Y ·r postcomp B g)
          ( left-whisker-comp²
            ( precomp f Y)
            ( inv-htpy (compute-htpy-postcomp-refl-htpy B g)))))
```
