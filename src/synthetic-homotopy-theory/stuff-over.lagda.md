# Stuff over other stuff

```agda
{-# OPTIONS --lossy-unification #-}
module synthetic-homotopy-theory.stuff-over where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-cubes-of-maps
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-identifications
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.transposition-identifications-along-equivalences
open import foundation.universe-levels
open import foundation.whiskering-higher-homotopies-composition
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-homotopies-concatenation
```

</details>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.functoriality-dependent-pair-types
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2}
  {A' : A → UU l3} {B' : B → UU l4}
  (f : A → B)
  (f' : (a : A) → A' a → B' (f a))
  where

  tot-map-over : Σ A A' → Σ B B'
  tot-map-over = map-Σ B' f f'

  coh-tot-map-over : coherence-square-maps tot-map-over pr1 pr1 f
  coh-tot-map-over = refl-htpy

module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2}
  {A' : A → UU l3} (B' : B → UU l4)
  {f g : A → B}
  (H : f ~ g)
  (f' : {a : A} → A' a → B' (f a))
  (g' : {a : A} → A' a → B' (g a))
  where

  htpy-over : UU (l1 ⊔ l3 ⊔ l4)
  htpy-over =
    {a : A} (a' : A' a) → dependent-identification B' (H a) (f' a') (g' a')

module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2}
  {A' : A → UU l3} (B' : B → UU l4)
  {f g : A → B}
  (H : f ~ g)
  (f' : {a : A} → A' a → B' (f a))
  (g' : {a : A} → A' a → B' (g a))
  where

  inv-htpy-over : htpy-over B' H f' g' → htpy-over B' (inv-htpy H) g' f'
  inv-htpy-over H' {a} a' = inv-dependent-identification B' (H a) (H' a')

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  compute-inv-dependent-identification :
    {x y : A} (p : x ＝ y) {x' : B x} {y' : B y} →
    (q : dependent-identification B p x' y') →
    inv-dependent-identification B p q ＝ map-eq-transpose-equiv-inv' (equiv-tr B p) (inv q)
  compute-inv-dependent-identification refl q = inv (right-unit ∙ ap-id (inv q))

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : A → UU l4} {B' : B → UU l5} {X' : X → UU l6}
  {f g : A → B}
  (H : f ~ g)
  {f' : {a : A} → A' a → B' (f a)}
  {g' : {a : A} → A' a → B' (g a)}
  (H' : htpy-over B' H f' g')
  (s : X → A) (s' : {x : X} → X' x → A' (s x))
  where

  right-whisk-htpy-over : htpy-over B' (H ·r s) (f' ∘ s') (g' ∘ s')
  right-whisk-htpy-over a' = H' (s' a')

module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2}
  {A' : A → UU l3} {B' : B → UU l4}
  where

  left-whisk-dependent-identification :
    {s : A → B} (s' : {a : A} → A' a → B' (s a))
    {x y : A} (p : x ＝ y)
    {x' : A' x} {y' : A' y} (q : dependent-identification A' p x' y') →
    dependent-identification B' (ap s p) (s' x') (s' y')
  left-whisk-dependent-identification s' refl q = ap s' q

  compute-left-whisk-dependent-identification :
    {s : A → B} (s' : {a : A} → A' a → B' (s a))
    {x y : A} (p : x ＝ y)
    {x' : A' x} {y' : A' y} (q : dependent-identification A' p x' y') →
    left-whisk-dependent-identification s' p q ＝
      substitution-law-tr B' s p ∙ inv (preserves-tr (λ a → s' {a}) p x') ∙ ap s' q
  compute-left-whisk-dependent-identification s' refl q = refl

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : A → UU l4} {B' : B → UU l5} {X' : X → UU l6}
  {f g : A → B}
  (H : f ~ g)
  {f' : {a : A} → A' a → B' (f a)}
  {g' : {a : A} → A' a → B' (g a)}
  (H' : htpy-over B' H f' g')
  {s : B → X} (s' : {b : B} → B' b → X' (s b))
  where

  LWMOTIF : {a : A} (a' : A' a) (g : A → B) (H : f ~ g) → UU (l5 ⊔ l6)
  LWMOTIF {a} a' g H =
    {g'a' : B' (g a)} →
    (H' : tr B' (H a) (f' a') ＝ g'a') →
    tr X' (ap s (H a)) (s' (f' a')) ＝ s' (g'a')

  left-whisk-htpy-over : htpy-over X' (s ·l H) (s' ∘ f') (s' ∘ g')
  left-whisk-htpy-over {a} a' = left-whisk-dependent-identification s' (H a) (H' a')

module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {A' : A → UU l3} {B' : B → UU l4}
  {f g h : A → B}
  (H : f ~ g) (K : g ~ h)
  {f' : {a : A} → A' a → B' (f a)}
  {g' : {a : A} → A' a → B' (g a)}
  {h' : {a : A} → A' a → B' (h a)}
  (H' : htpy-over B' H f' g') (K' : htpy-over B' K g' h')
  where

  concat-htpy-over : htpy-over B' (H ∙h K) f' h'
  concat-htpy-over {a} a' =
    concat-dependent-identification B' (H a) (K a) (H' a') (K' a')

module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {A' : A → UU l3} {B' : B → UU l4}
  (f : A → B)
  (f' : {a : A} → A' a → B' (f a))
  (sA : (a : A) → A' a)
  (sB : (b : B) → B' b)
  where

  section-map-over : UU (l1 ⊔ l4)
  section-map-over = (a : A) → f' (sA a) ＝ sB (f a)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  {A' : A → UU l4} {B' : B → UU l5} {C' : C → UU l6}
  (g : B → C) (f : A → B)
  (g' : {b : B} → B' b → C' (g b))
  (f' : {a : A} → A' a → B' (f a))
  (sA : (a : A) → A' a) (sB : (b : B) → B' b) (sC : (c : C) → C' c)
  where

  comp-section-map-over :
    section-map-over g g' sB sC → section-map-over f f' sA sB →
    section-map-over (g ∘ f) (g' ∘ f') sA sC
  comp-section-map-over G F =
    g' ·l F ∙h G ·r f

module _
  {l1 l2 : Level}
  {A : UU l1} {B : A → UU l2}
  {x y : A} (p : x ＝ y)
  {x' : B x} {y' : B y} (q : dependent-identification B p x' y')
  (s : (a : A) → B a)
  (F : x' ＝ s x) (G : y' ＝ s y)
  where

  section-dependent-identification : UU l2
  section-dependent-identification =
    q ∙ G ＝ ap (tr B p) F ∙ apd s p

module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {A' : A → UU l3} {B' : B → UU l4}
  {f g : A → B}
  (H : f ~ g)
  {f' : {a : A} → A' a → B' (f a)}
  {g' : {a : A} → A' a → B' (g a)}
  (H' : htpy-over B' H f' g')
  (sA : (a : A) → A' a)
  (sB : (b : B) → B' b)
  (F : section-map-over f f' sA sB)
  (G : section-map-over g g' sA sB)
  where

  section-htpy-over : UU (l1 ⊔ l4)
  section-htpy-over =
    (a : A) → section-dependent-identification (H a) (H' (sA a)) sB (F a) (G a)

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  inv-section-identification-over :
    {x y : A} (p : x ＝ y) →
    {x' : B x} {y' : B y} (q : dependent-identification B p x' y') →
    (s : (a : A) → B a) →
    (F : x' ＝ s x) (G : y' ＝ s y) →
    section-dependent-identification p q s F G →
    section-dependent-identification
      ( inv p)
      ( inv-dependent-identification B p q)
      ( s)
      ( G)
      ( F)
  inv-section-identification-over refl refl s F G α =
    inv (right-unit ∙ ap-id G ∙ α ∙ right-unit ∙ ap-id F)

module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {A' : A → UU l3} {B' : B → UU l4}
  {f g : A → B}
  (H : f ~ g)
  {f' : {a : A} → A' a → B' (f a)}
  {g' : {a : A} → A' a → B' (g a)}
  (H' : htpy-over B' H f' g')
  (sA : (a : A) → A' a)
  (sB : (b : B) → B' b)
  (F : section-map-over f f' sA sB)
  (G : section-map-over g g' sA sB)
  where

  inv-section-htpy-over :
    section-htpy-over H H' sA sB F G →
    section-htpy-over
      ( inv-htpy H)
      ( inv-htpy-over B' H f' g' H')
      ( sA)
      ( sB)
      ( G)
      ( F)
  inv-section-htpy-over α a =
    inv-section-identification-over (H a) (H' (sA a)) sB (F a) (G a) (α a)

module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {A' : A → UU l5} {B' : B → UU l6} {C' : C → UU l7} {D' : D → UU l8}
  {f : A → B} {g : B → C} {h : C → D}
  (f' : {a : A} → A' a → B' (f a))
  (g' : {b : B} → B' b → C' (g b))
  (h' : {c : C} → C' c → D' (h c))
  (sA : (a : A) → A' a)
  (sB : (b : B) → B' b)
  (sC : (c : C) → C' c)
  (sD : (d : D) → D' d)
  (F : section-map-over f f' sA sB)
  (G : section-map-over g g' sB sC)
  (H : section-map-over h h' sC sD)
  where

  assoc-comp-section-map-over :
    section-htpy-over
      ( refl-htpy {f = h ∘ g ∘ f})
      ( refl-htpy {f = h' ∘ g' ∘ f'})
      sA sD
      ( comp-section-map-over (h ∘ g) f (h' ∘ g') f' sA sB sD
        ( comp-section-map-over h g h' g' sB sC sD H G)
        ( F))
      ( comp-section-map-over h (g ∘ f) h' (g' ∘ f') sA sC sD H
        ( comp-section-map-over g f g' f' sA sB sC G F))
  assoc-comp-section-map-over =
    inv-htpy
      ( right-unit-htpy ∙h
        left-unit-law-left-whisker-comp _ ∙h
        inv-htpy-assoc-htpy ((h' ∘ g') ·l F) (h' ·l G ·r f) (H ·r (g ∘ f)) ∙h
        right-whisker-concat-htpy
          ( ( right-whisker-concat-htpy
              ( inv-preserves-comp-left-whisker-comp h' g' F)
              ( h' ·l G ·r f)) ∙h
            ( inv-htpy
              ( distributive-left-whisker-comp-concat h'
                ( g' ·l F)
                ( G ·r f))))
          ( H ·r g ·r f))

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : A → UU l4} {B' : B → UU l5} {X' : X → UU l6}
  {f g : A → B}
  (H : f ~ g)
  {f' : {a : A} → A' a → B' (f a)}
  {g' : {a : A} → A' a → B' (g a)}
  (H' : htpy-over B' H f' g')
  (sA : (a : A) → A' a)
  (sB : (b : B) → B' b)
  (F : section-map-over f f' sA sB)
  (G : section-map-over g g' sA sB)
  (α : section-htpy-over H H' sA sB F G)
  (s : X → A)
  (s' : {x : X} → X' x → A' (s x))
  (sX : (x : X) → X' x)
  (S : section-map-over s s' sX sA)
  where
  open import foundation.commuting-squares-of-identifications
  open import foundation.commuting-triangles-of-identifications

  right-whisk-section-htpy-over :
    section-htpy-over (H ·r s)
      ( right-whisk-htpy-over H H' s s')
      sX sB
      ( comp-section-map-over f s f' s' sX sA sB F S)
      ( comp-section-map-over g s g' s' sX sA sB G S)
  right-whisk-section-htpy-over x =
    right-whisker-concat-coherence-square-identifications
      ( ap (tr B' (H (s x)) ∘ f') (S x))
      ( H' (s' (sX x)))
      ( H' (sA (s x)))
      ( ap g' (S x))
      ( nat-htpy (H' {s x}) (S x))
      ( G (s x)) ∙
    ap (_∙ (H' (sA (s x)) ∙ G (s x))) (ap-comp (tr B' (H (s x))) f' (S x)) ∙
    ap (ap (tr B' (H (s x))) (ap f' (S x)) ∙_) (α (s x)) ∙
    right-whisker-concat-coherence-triangle-identifications'
      ( ap (tr B' (H (s x))) (ap f' (S x) ∙ F (s x)))
      ( ap (tr B' (H (s x))) (F (s x)))
      ( ap (tr B' (H (s x))) (ap f' (S x)))
      ( apd sB (H (s x)))
      ( inv (ap-concat (tr B' (H (s x))) (ap f' (S x)) (F (s x))))

module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {X : UU l2}
  {A' : A → UU l3} {X' : X → UU l4}
  where

  left-whisk-section-dependent-identification :
    {x y : A} (p : x ＝ y)
    {x' : A' x} {y' : A' y} (q : dependent-identification A' p x' y')
    (sA : (a : A) → A' a)
    (F : x' ＝ sA x) (G : y' ＝ sA y)
    (α : section-dependent-identification p q sA F G)
    {s : A → X} (s' : {a : A} → A' a → X' (s a))
    (sX : (x : X) → X' x)
    (S : section-map-over s s' sA sX) →
    section-dependent-identification
      ( ap s p)
      ( left-whisk-dependent-identification s' p q)
      sX (ap s' F ∙ S x) (ap s' G ∙ S y)
  left-whisk-section-dependent-identification {x} refl refl sA F G α s' sX S =
    ap (λ p → ap s' p ∙ S x) (α ∙ right-unit ∙ ap-id F) ∙
    inv (right-unit ∙ ap-id (ap s' F ∙ S x))

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : A → UU l4} {B' : B → UU l5} {X' : X → UU l6}
  {f g : A → B}
  (H : f ~ g)
  {f' : {a : A} → A' a → B' (f a)}
  {g' : {a : A} → A' a → B' (g a)}
  (H' : htpy-over B' H f' g')
  (sA : (a : A) → A' a)
  (sB : (b : B) → B' b)
  (F : section-map-over f f' sA sB)
  (G : section-map-over g g' sA sB)
  (α : section-htpy-over H H' sA sB F G)
  (s : B → X)
  (s' : {b : B} → B' b → X' (s b))
  (sX : (x : X) → X' x)
  (S : section-map-over s s' sB sX)
  where

  left-whisk-section-htpy-over :
    section-htpy-over (s ·l H)
      ( left-whisk-htpy-over H H' s')
      sA sX
      ( comp-section-map-over s f s' f' sA sB sX S F)
      ( comp-section-map-over s g s' g' sA sB sX S G)
  left-whisk-section-htpy-over a =
    left-whisk-section-dependent-identification (H a) (H' (sA a)) sB (F a) (G a) (α a) s' sX S

module _
  {l1 l2 : Level}
  {A : UU l1} {B : A → UU l2}
  where

  concat-section-dependent-identification :
    {x y z : A} (p : x ＝ y) (q : y ＝ z)
    {x' : B x} {y' : B y} {z' : B z}
    (p' : dependent-identification B p x' y')
    (q' : dependent-identification B q y' z')
    (s : (a : A) → B a)
    (F : x' ＝ s x) (G : y' ＝ s y) (H : z' ＝ s z)
    (α : section-dependent-identification p p' s F G)
    (β : section-dependent-identification q q' s G H) →
    section-dependent-identification (p ∙ q)
      ( concat-dependent-identification B p q p' q')
      ( s)
      ( F)
      ( H)
  concat-section-dependent-identification refl q refl q' s F G H α β =
    β ∙ ap (λ p → ap (tr B q) p ∙ apd s q) (α ∙ right-unit ∙ ap-id F)

module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {A' : A → UU l3} {B' : B → UU l4}
  {f g i : A → B}
  (H : f ~ g) (K : g ~ i)
  {f' : {a : A} → A' a → B' (f a)}
  {g' : {a : A} → A' a → B' (g a)}
  {i' : {a : A} → A' a → B' (i a)}
  (H' : htpy-over B' H f' g') (K' : htpy-over B' K g' i')
  (sA : (a : A) → A' a)
  (sB : (b : B) → B' b)
  (F : section-map-over f f' sA sB)
  (G : section-map-over g g' sA sB)
  (I : section-map-over i i' sA sB)
  (α : section-htpy-over H H' sA sB F G)
  (β : section-htpy-over K K' sA sB G I)
  where

  concat-section-htpy-over :
    section-htpy-over
      ( H ∙h K)
      ( concat-htpy-over H K H' K')
      ( sA)
      ( sB)
      ( F)
      ( I)
  concat-section-htpy-over a =
    concat-section-dependent-identification
      ( H a) (K a) (H' (sA a)) (K' (sA a)) sB (F a) (G a) (I a) (α a) (β a)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : A → UU l4} {B' : B → UU l5} {X' : X → UU l6}
  (f : A → B) (g : A → X) (m : B → X)
  (f' : {a : A} → A' a → B' (f a))
  (g' : {a : A} → A' a → X' (g a))
  (m' : {b : B} → B' b → X' (m b))
  (sA : (a : A) → A' a) (sB : (b : B) → B' b) (sX : (x : X) → X' x)
  (F : (a : A) → f' (sA a) ＝ sB (f a))
  (G : (a : A) → g' (sA a) ＝ sX (g a))
  (M : (b : B) → m' (sB b) ＝ sX (m b))
  where

  section-triangle-over :
    (H : coherence-triangle-maps g m f) →
    (H' : htpy-over X' H g' (m' ∘ f')) →
    UU (l1 ⊔ l6)
  section-triangle-over H H' =
    (a : A) →
    H' (sA a) ∙ ap m' (F a) ∙ (M (f a)) ＝
    ap (tr X' (H a)) (G a) ∙ apd sX (H a)

  unget-section-triangle-over :
    (H : coherence-triangle-maps g m f) →
    (H' : htpy-over X' H g' (m' ∘ f')) →
    section-triangle-over H H' →
    section-htpy-over H H' sA sX G
      ( comp-section-map-over m f m' f' sA sB sX M F)
  unget-section-triangle-over H H' α =
    inv-htpy-assoc-htpy (H' ·r sA) (m' ·l F) (M ·r f) ∙h α

  section-triangle-over' :
    (H : coherence-triangle-maps' g m f) →
    (H' : htpy-over X' H (m' ∘ f') g') →
    UU (l1 ⊔ l6)
  section-triangle-over' H H' =
    (a : A) →
    H' (sA a) ∙ G a ＝
    ap (tr X' (H a) ∘ m') (F a) ∙ ap (tr X' (H a)) (M (f a)) ∙ apd sX (H a)

  equiv-get-section-triangle-over' :
    (H : coherence-triangle-maps' g m f) →
    (H' : htpy-over X' H (m' ∘ f') g') →
    section-triangle-over' H H' ≃
    section-htpy-over H H' sA sX
      ( comp-section-map-over m f m' f' sA sB sX M F)
      ( G)
  equiv-get-section-triangle-over' H H' =
    equiv-Π-equiv-family
      ( λ a →
        equiv-concat'
          ( H' (sA a) ∙ G a)
          ( ap
            ( _∙ apd sX (H a))
            ( ( ap
                ( _∙ ap (tr X' (H a)) (M (f a)))
                ( ap-comp (tr X' (H a)) m' (F a))) ∙
              ( inv (ap-concat (tr X' (H a)) (ap m' (F a)) (M (f a)))))))

  unget-section-triangle-over' :
    (H : coherence-triangle-maps' g m f) →
    (H' : htpy-over X' H (m' ∘ f') g') →
    section-triangle-over' H H' →
    section-htpy-over H H' sA sX
      ( comp-section-map-over m f m' f' sA sB sX M F)
      ( G)
  unget-section-triangle-over' H H' =
    map-equiv (equiv-get-section-triangle-over' H H')

  get-section-triangle-over' :
    (H : coherence-triangle-maps' g m f) →
    (H' : htpy-over X' H (m' ∘ f') g') →
    section-htpy-over H H' sA sX
      ( comp-section-map-over m f m' f' sA sB sX M F)
      ( G) →
    section-triangle-over' H H'
  get-section-triangle-over' H H' =
    map-inv-equiv (equiv-get-section-triangle-over' H H')

  -- actually ≐ section-triangle-over 🤔
  -- section-triangle-over-inv :
  --   (H : coherence-triangle-maps g m f) →
  --   (H' : {a : A} (a' : A' a) → dependent-identification X' (H a) (g' a') (m' (f' a'))) →
  --   UU (l1 ⊔ l6)
  -- section-triangle-over-inv H H' =
  --   (a : A) →
  --   H' (sA a) ∙ ap m' (F a) ∙ (M (f a)) ＝
  --   ap (tr X' (H a)) (G a) ∙ apd sX (H a)

module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {P1 : UU l1} {P2 : UU l2} {P3 : UU l3} {P4 : UU l4}
  {Q1 : P1 → UU l5} {Q2 : P2 → UU l6} {Q3 : P3 → UU l7} {Q4 : P4 → UU l8}
  (g1 : P1 → P3) (f1 : P1 → P2) (f2 : P3 → P4) (g2 : P2 → P4)
  (g1' : {p : P1} → Q1 p → Q3 (g1 p))
  (f1' : {p : P1} → Q1 p → Q2 (f1 p))
  (f2' : {p : P3} → Q3 p → Q4 (f2 p))
  (g2' : {p : P2} → Q2 p → Q4 (g2 p))
  where

  square-over : coherence-square-maps g1 f1 f2 g2 → UU (l1 ⊔ l5 ⊔ l8)
  square-over H = htpy-over Q4 H (g2' ∘ f1') (f2' ∘ g1')

  module _
    (s1 : (p : P1) → Q1 p) (s2 : (p : P2) → Q2 p) (s3 : (p : P3) → Q3 p)
    (s4 : (p : P4) → Q4 p)
    (G1 : (p : P1) → g1' (s1 p) ＝ s3 (g1 p))
    (F1 : (p : P1) → f1' (s1 p) ＝ s2 (f1 p))
    (F2 : (p : P3) → f2' (s3 p) ＝ s4 (f2 p))
    (G2 : (p : P2) → g2' (s2 p) ＝ s4 (g2 p))
    (H : coherence-square-maps g1 f1 f2 g2)
    (H' : square-over H)
    where

    section-square-over : UU (l1 ⊔ l8)
    section-square-over =
      (p : P1) →
      H' (s1 p) ∙ ap f2' (G1 p) ∙ (F2 (g1 p)) ＝
      ( ap (tr Q4 (H p) ∘ g2') (F1 p) ∙
        ap (tr Q4 (H p)) (G2 (f1 p)) ∙
        apd s4 (H p))

    get-section-square-over :
      section-htpy-over H H' s1 s4
        ( comp-section-map-over g2 f1 g2' f1' s1 s2 s4 G2 F1)
        ( comp-section-map-over f2 g1 f2' g1' s1 s3 s4 F2 G1) →
      section-square-over
    get-section-square-over α =
      assoc-htpy (H' ·r s1) (f2' ·l G1) (F2 ·r g1) ∙h
      α ∙h
      ( λ p →
        ap
          ( _∙ apd s4 (H p))
          ( ap-concat (tr Q4 (H p)) (ap g2' (F1 p)) (G2 (f1 p)) ∙
            ap (_∙ _) (inv (ap-comp _ g2' (F1 p)))))

  module _
    (m : P2 → P3)
    (m' : {p : P2} → Q2 p → Q3 (m p))
    (B1 : coherence-triangle-maps' g1 m f1)
    (B2 : coherence-triangle-maps g2 f2 m)
    (T1 : htpy-over Q3 B1 (m' ∘ f1') g1')
    (T2 : htpy-over Q4 B2 g2' (f2' ∘ m'))
    where

    pasting-triangles-over :
      htpy-over Q4
        ( horizontal-pasting-up-diagonal-coherence-triangle-maps g1 f1 f2 g2 B1 B2)
        ( g2' ∘ f1')
        ( f2' ∘ g1')
    pasting-triangles-over =
      concat-htpy-over
        ( B2 ·r f1)
        ( f2 ·l B1)
        ( right-whisk-htpy-over B2 T2 f1 f1')
        ( left-whisk-htpy-over B1 T1 f2')

  module _
    (m : P2 → P3)
    (m' : {p : P2} → Q2 p → Q3 (m p))
    (s1 : (p : P1) → Q1 p) (s2 : (p : P2) → Q2 p) (s3 : (p : P3) → Q3 p)
    (s4 : (p : P4) → Q4 p)
    (G1 : (p : P1) → g1' (s1 p) ＝ s3 (g1 p))
    (F1 : (p : P1) → f1' (s1 p) ＝ s2 (f1 p))
    (F2 : (p : P3) → f2' (s3 p) ＝ s4 (f2 p))
    (G2 : (p : P2) → g2' (s2 p) ＝ s4 (g2 p))
    (M : (p : P2) → m' (s2 p) ＝ s3 (m p))
    (B1 : coherence-triangle-maps' g1 m f1)
    (B2 : coherence-triangle-maps g2 f2 m)
    (T1 : htpy-over Q3 B1 (m' ∘ f1') g1')
    (T2 : htpy-over Q4 B2 g2' (f2' ∘ m'))
    where

    pasting-sections-triangles-over :
      section-triangle-over' f1 g1 m f1' g1' m' s1 s2 s3 F1 G1 M B1 T1 →
      section-triangle-over m g2 f2 m' g2' f2' s2 s3 s4 M G2 F2 B2 T2 →
      section-square-over s1 s2 s3 s4 G1 F1 F2 G2
        ( horizontal-pasting-up-diagonal-coherence-triangle-maps g1 f1 f2 g2 B1 B2)
        ( pasting-triangles-over m m' B1 B2 T1 T2)
    pasting-sections-triangles-over S1 S2 =
      get-section-square-over s1 s2 s3 s4 G1 F1 F2 G2
        ( horizontal-pasting-up-diagonal-coherence-triangle-maps g1 f1 f2 g2 B1 B2)
        ( pasting-triangles-over m m' B1 B2 T1 T2)
        ( concat-section-htpy-over (B2 ·r f1) (f2 ·l B1)
           ( right-whisk-htpy-over B2 T2 f1 f1')
           ( left-whisk-htpy-over B1 T1 f2')
           s1 s4
           ( comp-section-map-over g2 f1 g2' f1' s1 s2 s4 G2 F1)
           ( comp-section-map-over (f2 ∘ m) f1 (f2' ∘ m') f1' s1 s2 s4
             ( comp-section-map-over f2 m f2' m' s2 s3 s4 F2 M)
             ( F1))
           ( comp-section-map-over f2 g1 f2' g1' s1 s3 s4 F2 G1)
           ( [ii])
           ( concat-section-htpy-over refl-htpy (f2 ·l B1) refl-htpy
             ( left-whisk-htpy-over B1 T1 f2')
             s1 s4 _ _ _
             ( assoc-comp-section-map-over f1' m' f2' s1 s2 s3 s4 F1 M F2)
             ( [iv])))
      where
        [i] =
          unget-section-triangle-over m g2 f2 m' g2' f2' s2 s3 s4 M G2 F2 B2 T2 S2
        [ii] = right-whisk-section-htpy-over B2 T2 s2 s4 _ _ [i] f1 f1' s1 F1
        [iii] =
          unget-section-triangle-over' f1 g1 m f1' g1' m' s1 s2 s3 F1 G1 M B1 T1 S1
        [iv] = left-whisk-section-htpy-over B1 T1 s1 s3 _ _ [iii] f2 f2' s4 F2
```

```agda
-- open import foundation.sections
-- open import foundation.transport-along-homotopies
-- module _
--   {l1 l2 : Level}
--   {A : UU l1} (B : A → UU l2)
--   where

--   sect-section :
--     section (pr1 {B = B}) →
--     ((a : A) → B a)
--   sect-section (s , H) a = tr B (H a) (pr2 (s a))

--   section-sect :
--     ((a : A) → B a) →
--     section (pr1 {B = B})
--   section-sect = section-dependent-function

-- module _
--   {l1 l2 l3 l4 : Level}
--   {A : UU l1} {B : UU l2} {A' : UU l3} {B' : UU l4}
--   (f : A → B) (f' : A' → B')
--   where

--   htpy-hom-map :
--     (hA : A' → A) (hB : B' → B) →
--     coherence-square-maps f' hA hB f →
--     (hA' : A' → A) (hB' : B' → B) →
--     coherence-square-maps f' hA' hB' f →
--     hA ~ hA' → hB ~ hB' →
--     UU (l2 ⊔ l3)
--   htpy-hom-map hA hB H hA' hB' H' σA σB = H ∙h (σB ·r f') ~ (f ·l σA) ∙h H'

-- module _
--   {l1 l2 l3 l4 l5 l6 : Level}
--   {A : UU l1} {B : UU l2} {C : UU l3}
--   {X : UU l4} {Y : UU l5} {Z : UU l6}
--   (f : A → B) (g : B → C)
--   (f' : X → Y) (g' : Y → Z)
--   (hA hA' : X → A) (hB hB' : Y → B) (hC hC' : Z → C)
--   (σA : hA ~ hA') (σB : hB ~ hB') (σC : hC ~ hC')
--   (NL : coherence-square-maps f' hA hB f)
--   (FL : coherence-square-maps f' hA' hB' f)
--   (α : htpy-hom-map f f' hA hB NL hA' hB' FL σA σB)
--   (NR : coherence-square-maps g' hB hC g)
--   (FR : coherence-square-maps g' hB' hC' g)
--   (β : htpy-hom-map g g' hB hC NR hB' hC' FR σB σC)
--   where
--   open import foundation.commuting-squares-of-homotopies

--   comp-htpy-hom-map :
--     htpy-hom-map (g ∘ f) (g' ∘ f')
--       hA hC
--       ( pasting-horizontal-coherence-square-maps f' g' hA hB hC f g NL NR)
--       hA' hC'
--       ( pasting-horizontal-coherence-square-maps f' g' hA' hB' hC' f g FL FR)
--       σA σC
--   comp-htpy-hom-map =
--     left-whisker-concat-coherence-square-homotopies (g ·l NL)
--       ( g ·l σB ·r f') (NR ·r f') (FR ·r f') (σC ·r (g' ∘ f'))
--       ( β ·r f') ∙h
--     right-whisker-concat-htpy
--       ( inv-htpy
--           ( distributive-left-whisker-comp-concat g NL (σB ·r f')) ∙h
--         left-whisker-comp² g α ∙h
--         distributive-left-whisker-comp-concat g (f ·l σA) FL ∙h
--         right-whisker-concat-htpy
--           ( preserves-comp-left-whisker-comp g f σA)
--           ( g ·l FL))
--       ( FR ·r f') ∙h
--     assoc-htpy ((g ∘ f) ·l σA) (g ·l FL) (FR ·r f')

-- module _
--   {l1 l2 l3 l4 : Level}
--   {A : UU l1} {B : UU l2} {A' : UU l3} {B' : UU l4}
--   (f : A → B) (f' : A' → B')
--   (hA : A' → A) (hB : B' → B)
--   (H : coherence-square-maps f' hA hB f)
--   where

--   section-displayed-map-over : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
--   section-displayed-map-over =
--     Σ ( section hA)
--       ( λ sA →
--         Σ ( section hB)
--           ( λ sB →
--             Σ ( coherence-square-maps
--                 f (map-section hA sA) (map-section hB sB) f')
--               ( λ K →
--                 htpy-hom-map f f
--                   ( hA ∘ map-section hA sA)
--                   ( hB ∘ map-section hB sB)
--                   ( pasting-vertical-coherence-square-maps f
--                     ( map-section hA sA) (map-section hB sB) f' hA hB f K H)
--                   id id refl-htpy
--                   ( is-section-map-section hA sA)
--                   ( is-section-map-section hB sB))))

-- module _
--   {l1 l2 l3 l4 : Level}
--   {A : UU l1} {P : A → UU l2}
--   {B : UU l3} {Q : B → UU l4}
--   (f : A → B)
--   (f' : {a : A} → P a → Q (f a))
--   where

--   sect-map-over-section-map-over :
--     (s :
--       section-displayed-map-over f
--         (tot-map-over f (λ a → f' {a}))
--         pr1 pr1 refl-htpy) →
--     section-map-over f
--       ( f')
--       ( sect-section P (pr1 s))
--       ( sect-section Q (pr1 (pr2 s)))
--   sect-map-over-section-map-over (sA , sB , H , α) a =
--     ( preserves-tr (λ a → f' {a}) (σA a) (sA2 a)) ∙
--     ( inv (substitution-law-tr Q f (σA a))) ∙
--     ( ap (λ p → tr Q p (f' (sA2 a))) (inv (α a ∙ right-unit))) ∙
--     ( tr-concat (H1 a) (σB (f a)) (f' (sA2 a))) ∙
--     ( ap
--       ( tr Q (σB (f a)))
--       ( substitution-law-tr Q pr1 (H a) ∙ apd pr2 (H a)))
--     where
--       sA1 : A → A
--       sA1 = pr1 ∘ map-section pr1 sA
--       σA : sA1 ~ id
--       σA = is-section-map-section pr1 sA
--       sA2 : (a : A) → P (sA1 a)
--       sA2 = pr2 ∘ map-section pr1 sA
--       sB1 : B → B
--       sB1 = pr1 ∘ map-section pr1 sB
--       σB : sB1 ~ id
--       σB = is-section-map-section pr1 sB
--       H1 : f ∘ sA1 ~ sB1 ∘ f
--       H1 = pr1 ·l H
-- ```

-- ```agda
-- module _
--   {l1 l2 : Level}
--   {A : UU l1} {B : A → UU l2}
--   (s : (a : A) → B a)
--   where

--   ap-map-section-family-lemma :
--     {a a' : A} (p : a ＝ a') →
--     ap (map-section-family s) p ＝ eq-pair-Σ p (apd s p)
--   ap-map-section-family-lemma refl = refl
-- module _
--   {l1 l2 l3 : Level}
--   {A : UU l1} {B : UU l2} {Q : B → UU l3}
--   (s : (b : B) → Q b)
--   {f g : A → B} (H : f ~ g)
--   where

--   left-whisker-dependent-function-lemma :
--     (a : A) →
--     (map-section-family s ·l H) a ＝ eq-pair-Σ (H a) (apd s (H a))
--   left-whisker-dependent-function-lemma a = ap-map-section-family-lemma s (H a)
-- module _
--   {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
--   where
--   concat-vertical-eq-pair :
--     {x y : A} (p : x ＝ y) {x' : B x} {y' z' : B y} →
--     (q : dependent-identification B p x' y') → (r : y' ＝ z') →
--     eq-pair-Σ p (q ∙ r) ＝ eq-pair-Σ p q ∙ eq-pair-eq-fiber r
--   concat-vertical-eq-pair {x} refl q r = ap-concat (pair x) q r
-- module _
--   {l1 l2 l3 l4 : Level}
--   {A : UU l1} {B : UU l2}
--   {A' : A → UU l3} {B' : B → UU l4}
--   {f : A → B} (f' : (a : A) → A' a → B' (f a))
--   where

--   ap-map-Σ-eq-fiber :
--     {a : A} (x y : A' a) (p : x ＝ y) →
--     ap (map-Σ B' f f') (eq-pair-eq-fiber p) ＝ eq-pair-eq-fiber (ap (f' a) p)
--   ap-map-Σ-eq-fiber x .x refl = refl

--   -- ap-map-Σ-eq-fiber' :
--   --   {a : A} (x y : A' a) (p : x ＝ y) →
--   --   ap (map-Σ B' f f') (eq-pair-eq-fiber p) ＝ eq-pair-eq-fiber (ap (f' a) p)
--   -- ap-map-Σ-eq-fiber' {a} x y p =
--   --   compute-ap-eq-pair-Σ (map-Σ B' f f') refl p ∙
--   --   ap-comp (pair (f a)) (f' a) p
-- module _
--   {l1 l2 l3 l4 l5 l6 : Level}
--   {A : UU l1} {B : UU l2} {C : UU l3}
--   {A' : A → UU l4} {B' : B → UU l5} {C' : C → UU l6}
--   {f : A → B} {g : B → C}
--   (f' : (a : A) → A' a → B' (f a))
--   (g' : (b : B) → B' b → C' (g b))
--   (sA : (a : A) → A' a) (sB : (b : B) → B' b) (sC : (c : C) → C' c)
--   (F : (a : A) → f' a (sA a) ＝ sB (f a)) (G : (b : B) → g' b (sB b) ＝ sC (g b))
--   where

--   pasting-horizontal-comp :
--     pasting-horizontal-coherence-square-maps f g
--       ( map-section-family sA) (map-section-family sB) (map-section-family sC)
--       ( tot-map-over f f') (tot-map-over g g')
--       ( eq-pair-eq-fiber ∘ F)
--       ( eq-pair-eq-fiber ∘ G) ~
--     eq-pair-eq-fiber ∘
--       ((g' _) ·l F ∙h G ·r f)
--   pasting-horizontal-comp a =
--     ap
--       ( _∙ eq-pair-eq-fiber (G (f a)))
--       ( inv (ap-comp (tot-map-over g g') (pair (f a)) (F a)) ∙
--         ap-comp (pair (g (f a))) (g' (f a)) (F a)) ∙
--     inv (ap-concat (pair (g (f a))) (ap (g' (f a)) (F a)) (G (f a)))

-- module _
--   {l1 l2 l3 l4 : Level}
--   {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
--   {f g : A → B} {f' g' : X → Y}
--   (top : f' ~ g') (bottom : f ~ g)
--   {hA : X → A} {hB : Y → B}
--   (N : f ∘ hA ~ hB ∘ f') (F : g ∘ hA ~ hB ∘ g')
--   where

--   hom-htpy : UU (l2 ⊔ l3)
--   hom-htpy = N ∙h (hB ·l top) ~ (bottom ·r hA) ∙h F

-- -- module _
-- --   where

-- --   alt-map-coherence-square-homotopies

-- module _
--   {l1 l2 l3 l4 l5 l6 : Level}
--   {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {V : UU l5} {W : UU l6}
--   {f g : A → B} {f' g' : X → Y} {f'' g'' : V → W}
--   (mid : f' ~ g') (bottom : f ~ g) (top : f'' ~ g'')
--   {hA : X → A} {hB : Y → B} {hA' : V → X} {hB' : W → Y}
--   (bottom-N : f ∘ hA ~ hB ∘ f') (bottom-F : g ∘ hA ~ hB ∘ g')
--   (top-N : f' ∘ hA' ~ hB' ∘ f'') (top-F : g' ∘ hA' ~ hB' ∘ g'')
--   where

--   pasting-vertical-hom-htpy :
--     hom-htpy mid bottom {hB = hB} bottom-N bottom-F →
--     hom-htpy top mid {hB = hB'} top-N top-F →
--     hom-htpy top bottom {hB = hB ∘ hB'}
--       ( pasting-vertical-coherence-square-maps f'' hA' hB' f' hA hB f
--         top-N bottom-N)
--       ( pasting-vertical-coherence-square-maps g'' hA' hB' g' hA hB g
--         top-F bottom-F)
--   pasting-vertical-hom-htpy α β =
--     left-whisker-concat-coherence-square-homotopies
--       ( bottom-N ·r hA')
--       ( hB ·l mid ·r hA')
--       ( hB ·l top-N)
--       ( hB ·l top-F)
--       ( (hB ∘ hB') ·l top)
--       ( left-whisker-concat-htpy (hB ·l top-N)
--           ( inv-htpy (preserves-comp-left-whisker-comp hB hB' top)) ∙h
--         map-coherence-square-homotopies hB (mid ·r hA') top-N top-F (hB' ·l top)
--           ( β)) ∙h
--     right-whisker-concat-htpy (α ·r hA') (hB ·l top-F) ∙h
--     assoc-htpy (bottom ·r (hA ∘ hA')) (bottom-F ·r hA') (hB ·l top-F)

-- module _
--   {l1 l2 : Level}
--   {A : UU l1} {B : UU l2}
--   {f g : A → B} (H : f ~ g)
--   where

--   id-hom-htpy : hom-htpy H H {hA = id} {hB = id} refl-htpy refl-htpy
--   id-hom-htpy = left-unit-law-left-whisker-comp H ∙h inv-htpy-right-unit-htpy

-- module _
--   {l1 l2 l3 l4 : Level}
--   {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
--   (f g : A → B) (f' g' : X → Y)
--   (bottom : f ~ g) (top : f' ~ g')
--   (hA : X → A) (hB : Y → B)
--   (N : f ∘ hA ~ hB ∘ f') (F : g ∘ hA ~ hB ∘ g')
--   (α : hom-htpy top bottom N F)
--   (hA' : X → A) (hB' : Y → B)
--   (N' : f ∘ hA' ~ hB' ∘ f') (F' : g ∘ hA' ~ hB' ∘ g')
--   (β : hom-htpy top bottom N' F')
--   (σA : hA ~ hA') (σB : hB ~ hB')
--   (γN : htpy-hom-map f f' hA hB N hA' hB' N' σA σB)
--   (γF : htpy-hom-map g g' hA hB F hA' hB' F' σA σB)
--   where

--   nudged-α nudged-β :
--     (N ∙h (hB ·l top)) ∙h (σB ·r g') ~
--     (f ·l σA) ∙h ((bottom ·r hA') ∙h F')
--   nudged-α =
--     right-whisker-concat-htpy α (σB ·r g') ∙h
--     assoc-htpy (bottom ·r hA) F (σB ·r g') ∙h
--     left-whisker-concat-htpy (bottom ·r hA) γF ∙h
--     right-whisker-concat-coherence-square-homotopies
--       ( f ·l σA)
--       ( bottom ·r hA)
--       ( bottom ·r hA')
--       ( g ·l σA)
--       ( λ x → nat-htpy bottom (σA x))
--       ( F')
--   nudged-β =
--     left-whisker-concat-coherence-square-homotopies N
--       ( σB ·r f')
--       ( hB ·l top)
--       ( hB' ·l top)
--       ( σB ·r g')
--       ( λ x → inv (nat-htpy σB (top x))) ∙h
--     right-whisker-concat-htpy γN (hB' ·l top) ∙h
--     assoc-htpy (f ·l σA) N' (hB' ·l top) ∙h
--     left-whisker-concat-htpy (f ·l σA) β

--   htpy-hom-htpy : UU (l2 ⊔ l3)
--   htpy-hom-htpy = nudged-α ~ nudged-β

-- module _
--   {l1 l2 l3 l4 : Level}
--   {A : UU l1} {B : UU l2} {A' : UU l3} {B' : UU l4}
--   {f' g' : A' → B'} (top : f' ~ g')
--   {f g : A → B} (bottom : f ~ g)
--   (hA : A' → A) (hB : B' → B)
--   (N : coherence-square-maps f' hA hB f)
--   (F : coherence-square-maps g' hA hB g)
--   (α : hom-htpy top bottom {hB = hB} N F)
--   where

--   coh-section-hom-htpy :
--     (sA : section hA) (sB : section hB)
--     (sN : coherence-square-maps f (map-section hA sA) (map-section hB sB) f')
--     (sF : coherence-square-maps g (map-section hA sA) (map-section hB sB) g')
--     (β : hom-htpy bottom top {hB = map-section hB sB} sN sF)
--     (γN :
--       htpy-hom-map f f
--         ( hA ∘ map-section hA sA) (hB ∘ map-section hB sB)
--         ( pasting-vertical-coherence-square-maps f
--           ( map-section hA sA) (map-section hB sB)
--           f' hA hB f sN N)
--         id id refl-htpy
--         ( is-section-map-section hA sA)
--         ( is-section-map-section hB sB))
--     (γF :
--       htpy-hom-map g g
--         ( hA ∘ pr1 sA) (hB ∘ pr1 sB)
--         ( pasting-vertical-coherence-square-maps g (pr1 sA) (pr1 sB) g' hA
--           hB g sF F)
--         id id refl-htpy (pr2 sA) (pr2 sB)) →
--     UU (l1 ⊔ l2)
--   coh-section-hom-htpy sA sB sN sF β =
--     htpy-hom-htpy f g f g bottom bottom
--       ( hA ∘ map-section hA sA)
--       ( hB ∘ map-section hB sB)
--       ( pasting-vertical-coherence-square-maps f map-sA map-sB f' hA hB f sN N)
--       ( pasting-vertical-coherence-square-maps g map-sA map-sB g' hA hB g sF F)
--       ( pasting-vertical-hom-htpy top bottom bottom N F sN sF α β)
--       id id refl-htpy refl-htpy (id-hom-htpy bottom)
--       ( is-section-map-section hA sA)
--       ( is-section-map-section hB sB)
--     where
--       map-sA : A → A'
--       map-sA = map-section hA sA
--       map-sB : B → B'
--       map-sB = map-section hB sB

-- module _
--   {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
--   where

--   compute-concat-dependent-identification-right-base-refl :
--     { x y : A} (p : x ＝ y) →
--     { x' : B x} {y' z' : B y} (p' : dependent-identification B p x' y') →
--     ( q' : y' ＝ z') →
--     concat-dependent-identification B p refl p' q' ＝ ap (λ r → tr B r x') right-unit ∙ p' ∙ q'
--   compute-concat-dependent-identification-right-base-refl refl p' q' = ap (_∙ q') (ap-id p')

--   interchange-concat-eq-pair-Σ-left :
--     {y z : A} (q : y ＝ z) {x' y' : B y} {z' : B z} →
--     (p' : x' ＝ y')
--     (q' : dependent-identification B q y' z') →
--     eq-pair-eq-fiber p' ∙ eq-pair-Σ q q' ＝
--     eq-pair-Σ q (ap (tr B q) p' ∙ q')
--   interchange-concat-eq-pair-Σ-left q refl q' = refl

--   interchange-concat-eq-pair-Σ-right :
--     {x y : A} (p : x ＝ y) {x' : B x} {y' z' : B y} →
--     (p' : dependent-identification B p x' y') →
--     (q' : y' ＝ z') →
--     eq-pair-Σ p p' ∙ eq-pair-eq-fiber q' ＝
--     eq-pair-Σ p (p' ∙ q')
--   interchange-concat-eq-pair-Σ-right p p' refl =
--     right-unit ∙ ap (eq-pair-Σ p) (inv right-unit)

-- module _
--   {l1 l2 l3 l4 : Level}
--   {A : UU l1} {B : UU l2} {P : A → UU l3} {Q : B → UU l4}
--   {f g : A → B} (H : f ~ g)
--   {f' : (a : A) → P a → Q (f a)} {g' : (a : A) → P a → Q (g a)}
--   (H' : htpy-over Q H (f' _) (g' _))
--   (sA : (a : A) → P a)
--   (sB : (b : B) → Q b)
--   (F : section-map-over f (f' _) sA sB)
--   (G : section-map-over g (g' _) sA sB)
--   (α : section-htpy-over H H' sA sB F G)
--   where
--   open import foundation.embeddings

--   _ : coh-section-hom-htpy
--     ( λ p → eq-pair-Σ (H (pr1 p)) (H' (pr2 p)))
--     ( H)
--     pr1 pr1 refl-htpy refl-htpy
--     ( λ p → ap-pr1-eq-pair-Σ (H (pr1 p)) (H' (pr2 p)) ∙ inv right-unit)
--     ( section-dependent-function sA)
--     ( section-dependent-function sB)
--     ( eq-pair-eq-fiber ∘ F)
--     ( eq-pair-eq-fiber ∘ G)
--     -- The point is that this will be `ap pr1`'d, so the α in the fiber is
--     -- projected away. This definition should probably be defined in a nicer way
--     -- to make the proof less opaque.
--     ( λ a →
--       ap (eq-pair-eq-fiber (F a) ∙_) (ap-map-section-family-lemma sB (H a)) ∙
--       interchange-concat-eq-pair-Σ-left (H a) (F a) (apd sB (H a)) ∙
--       ap (eq-pair-Σ (H a)) (inv (α a)) ∙
--       inv (interchange-concat-eq-pair-Σ-right (H a) (H' (sA a)) (G a)))
--     ( λ a → right-unit ∙ ap-pr1-eq-pair-eq-fiber (F a))
--     ( λ a → right-unit ∙ ap-pr1-eq-pair-eq-fiber (G a))
--   _ = {!!}

-- -- module _
-- --   {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
-- --   {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
-- --   (f : A → B) (g : A → C) (h : B → D) (k : C → D)
-- --   {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
-- --   (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
-- --   (top : h' ∘ f' ~ k' ∘ g')
-- --   (bottom : h ∘ f ~ k ∘ g)
-- --   (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
-- --   (back-left : (f ∘ hA) ~ (hB ∘ f'))
-- --   (back-right : (g ∘ hA) ~ (hC ∘ g'))
-- --   (front-left : (h ∘ hB) ~ (hD ∘ h'))
-- --   (front-right : (k ∘ hC) ~ (hD ∘ k'))
-- --   (α :
-- --     coherence-cube-maps f g h k f' g' h' k' hA hB hC hD
-- --       top back-left back-right front-left front-right bottom)
-- --   (hA' : A' → A) (hB' : B' → B) (hC' : C' → C) (hD' : D' → D)
-- --   (back-left' : (f ∘ hA') ~ (hB' ∘ f'))
-- --   (back-right' : (g ∘ hA') ~ (hC' ∘ g'))
-- --   (front-left' : (h ∘ hB') ~ (hD' ∘ h'))
-- --   (front-right' : (k ∘ hC') ~ (hD' ∘ k'))
-- --   (β :
-- --     coherence-cube-maps f g h k f' g' h' k' hA' hB' hC' hD'
-- --       top back-left' back-right' front-left' front-right' bottom)
-- --   (σA : hA ~ hA') (σB : hB ~ hB') (σC : hC ~ hC') (σD : hD ~ hD')
-- --   (back-left-H : htpy-hom-map f f' hA hB back-left hA' hB' back-left' σA σB)
-- --   (back-right-H : htpy-hom-map g g' hA hC back-right hA' hC' back-right' σA σC)
-- --   (front-left-H : htpy-hom-map h h' hB hD front-left hB' hD' front-left' σB σD)
-- --   (front-right-H : htpy-hom-map k k' hC hD front-right hC' hD' front-right' σC σD)
-- --   where
-- --   open import foundation.commuting-squares-of-homotopies

-- --   htpy-hom-square :
-- --     UU (l4 ⊔ l1')
-- --   htpy-hom-square =
-- --     htpy-hom-htpy (h ∘ f) (k ∘ g) (h' ∘ f') (k' ∘ g') bottom top hA hD
-- --       ( pasting-horizontal-coherence-square-maps f' h' hA hB hD f h back-left front-left)
-- --       ( pasting-horizontal-coherence-square-maps g' k' hA hC hD g k back-right front-right)
-- --       ( α)
-- --       hA' hD'
-- --       ( pasting-horizontal-coherence-square-maps f' h' hA' hB' hD' f h back-left' front-left')
-- --       ( pasting-horizontal-coherence-square-maps g' k' hA' hC' hD' g k back-right' front-right')
-- --       ( β)
-- --       σA σD
-- --       ( comp-htpy-hom-map f h f' h' hA hA' hB hB' hD hD' σA σB σD
-- --         back-left back-left' back-left-H
-- --         front-left front-left' front-left-H)
-- --       ( comp-htpy-hom-map g k g' k' hA hA' hC hC' hD hD' σA σC σD
-- --         back-right back-right' back-right-H
-- --         front-right front-right' front-right-H)

-- -- module _
-- --   {l1 l2 l3 l4 : Level}
-- --   {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
-- --   (f : A → B) (g : A → C) (h : B → D) (k : C → D)
-- --   (H : coherence-square-maps g f k h)
-- --   where

-- --   id-cube :
-- --     coherence-cube-maps f g h k f g h k id id id id
-- --       H refl-htpy refl-htpy refl-htpy refl-htpy H
-- --   id-cube = left-unit-law-left-whisker-comp H ∙h inv-htpy-right-unit-htpy

-- -- module _
-- --   {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
-- --   {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
-- --   (f : A → B) (g : A → C) (h : B → D) (k : C → D)
-- --   {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
-- --   (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
-- --   (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
-- --   (top : (h' ∘ f') ~ (k' ∘ g'))
-- --   (back-left : (f ∘ hA) ~ (hB ∘ f'))
-- --   (back-right : (g ∘ hA) ~ (hC ∘ g'))
-- --   (front-left : (h ∘ hB) ~ (hD ∘ h'))
-- --   (front-right : (k ∘ hC) ~ (hD ∘ k'))
-- --   (bottom : (h ∘ f) ~ (k ∘ g))
-- --   (α :
-- --     coherence-cube-maps f g h k f' g' h' k' hA hB hC hD
-- --       top back-left back-right front-left front-right bottom)
-- --   where

-- --   section-displayed-cube-over : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l1' ⊔ l2' ⊔ l3' ⊔ l4')
-- --   section-displayed-cube-over =
-- --     Σ ( section-displayed-map-over f f' hA hB back-left)
-- --       ( λ sF →
-- --         Σ ( section-displayed-map-over k k' hC hD front-right)
-- --           ( λ sK →
-- --             Σ ( coherence-square-maps g
-- --                 ( map-section hA (pr1 sF))
-- --                 ( map-section hC (pr1 sK))
-- --                 ( g'))
-- --               ( λ G →
-- --                 Σ ( htpy-hom-map g g
-- --                     ( hA ∘ map-section hA (pr1 sF))
-- --                     ( hC ∘ map-section hC (pr1 sK))
-- --                     ( pasting-vertical-coherence-square-maps g
-- --                       ( map-section hA (pr1 sF))
-- --                       ( map-section hC (pr1 sK))
-- --                       g' hA hC g
-- --                       G back-right)
-- --                     id id refl-htpy
-- --                     ( is-section-map-section hA (pr1 sF))
-- --                     ( is-section-map-section hC (pr1 sK)))
-- --                   ( λ sG →
-- --                     Σ ( coherence-square-maps h
-- --                         ( map-section hB (pr1 (pr2 sF)))
-- --                         ( map-section hD (pr1 (pr2 sK)))
-- --                         ( h'))
-- --                       ( λ H →
-- --                         Σ ( htpy-hom-map h h
-- --                             ( hB ∘ map-section hB (pr1 (pr2 sF)))
-- --                             ( hD ∘ map-section hD (pr1 (pr2 sK)))
-- --                             ( pasting-vertical-coherence-square-maps h
-- --                               ( map-section hB (pr1 (pr2 sF)))
-- --                               ( map-section hD (pr1 (pr2 sK)))
-- --                               h' hB hD h
-- --                               H front-left)
-- --                             id id refl-htpy
-- --                             ( is-section-map-section hB (pr1 (pr2 sF)))
-- --                             ( is-section-map-section hD (pr1 (pr2 sK))))
-- --                           ( λ sH →
-- --                             Σ ( coherence-cube-maps f' g' h' k' f g h k
-- --                                 ( map-section hA (pr1 sF))
-- --                                 ( map-section hB (pr1 (pr2 sF)))
-- --                                 ( map-section hC (pr1 sK))
-- --                                 ( map-section hD (pr1 (pr2 sK)))
-- --                                 ( bottom)
-- --                                 ( pr1 (pr2 (pr2 sF)))
-- --                                 ( G)
-- --                                 ( H)
-- --                                 ( pr1 (pr2 (pr2 sK)))
-- --                                 ( top))
-- --                               ( λ β →
-- --                                 htpy-hom-square f g h k f g h k bottom bottom
-- --                                   ( hA ∘ map-section hA (pr1 sF))
-- --                                   ( hB ∘ map-section hB (pr1 (pr2 sF)))
-- --                                   ( hC ∘ map-section hC (pr1 sK))
-- --                                   ( hD ∘ map-section hD (pr1 (pr2 sK)))
-- --                                   ( pasting-vertical-coherence-square-maps f
-- --                                     ( map-section hA (pr1 sF))
-- --                                     ( map-section hB (pr1 (pr2 sF)))
-- --                                     f' hA hB f
-- --                                     ( pr1 (pr2 (pr2 sF)))
-- --                                     ( back-left))
-- --                                   ( pasting-vertical-coherence-square-maps g
-- --                                     ( map-section hA (pr1 sF))
-- --                                     ( map-section hC (pr1 sK))
-- --                                     g' hA hC g
-- --                                     ( G)
-- --                                     ( back-right))
-- --                                   ( pasting-vertical-coherence-square-maps h
-- --                                     ( map-section hB (pr1 (pr2 sF)))
-- --                                     ( map-section hD (pr1 (pr2 sK)))
-- --                                     h' hB hD h
-- --                                     ( H)
-- --                                     ( front-left))
-- --                                   ( pasting-vertical-coherence-square-maps k
-- --                                     ( map-section hC (pr1 sK))
-- --                                     ( map-section hD (pr1 (pr2 sK)))
-- --                                     k' hC hD k
-- --                                     ( pr1 (pr2 (pr2 sK)))
-- --                                     ( front-right))
-- --                                   ( pasting-vertical-coherence-cube-maps f g h k
-- --                                     f' g' h' k' f g h k
-- --                                     hA hB hC hD
-- --                                     ( map-section hA (pr1 sF))
-- --                                     ( map-section hB (pr1 (pr2 sF)))
-- --                                     ( map-section hC (pr1 sK))
-- --                                     ( map-section hD (pr1 (pr2 sK)))
-- --                                     ( top)
-- --                                     back-left back-right front-left front-right bottom
-- --                                     ( bottom)
-- --                                     ( pr1 (pr2 (pr2 sF)))
-- --                                     ( G)
-- --                                     ( H)
-- --                                     ( pr1 (pr2 (pr2 sK)))
-- --                                     ( α)
-- --                                     ( β))
-- --                                   id id id id
-- --                                   refl-htpy refl-htpy refl-htpy refl-htpy
-- --                                   ( id-cube f g h k bottom)
-- --                                   ( is-section-map-section hA (pr1 sF))
-- --                                   ( is-section-map-section hB (pr1 (pr2 sF)))
-- --                                   ( is-section-map-section hC (pr1 sK))
-- --                                   ( is-section-map-section hD (pr1 (pr2 sK)))
-- --                                   ( pr2 (pr2 (pr2 sF)))
-- --                                   ( sG)
-- --                                   ( sH)
-- --                                   ( pr2 (pr2 (pr2 sK))))))))))

-- -- module _
-- --   {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
-- --   {P1 : UU l1} {P2 : UU l2} {P3 : UU l3} {P4 : UU l4}
-- --   {Q1 : P1 → UU l5} {Q2 : P2 → UU l6} {Q3 : P3 → UU l7} {Q4 : P4 → UU l8}
-- --   (g1 : P1 → P3) (f1 : P1 → P2) (f2 : P3 → P4) (g2 : P2 → P4)
-- --   (g1' : (p : P1) → Q1 p → Q3 (g1 p))
-- --   (f1' : (p : P1) → Q1 p → Q2 (f1 p))
-- --   (f2' : (p : P3) → Q3 p → Q4 (f2 p))
-- --   (g2' : (p : P2) → Q2 p → Q4 (g2 p))
-- --   (bottom : g2 ∘ f1 ~ f2 ∘ g1)
-- --   (top : square-over g1 f1 f2 g2 (g1' _) (f1' _) (f2' _) (g2' _) bottom)
-- --   where

-- --   tot-square-over :
-- --     coherence-square-maps
-- --       ( tot-map-over g1 g1')
-- --       ( tot-map-over f1 f1')
-- --       ( tot-map-over {B' = Q4} f2 f2')
-- --       ( tot-map-over g2 g2')
-- --   tot-square-over =
-- --     coherence-square-maps-Σ Q4 g1' f1' f2' g2' (λ p → top {p})

-- --   coh-tot-square-over :
-- --     coherence-cube-maps f1 g1 g2 f2
-- --       ( map-Σ Q2 f1 f1')
-- --       ( map-Σ Q3 g1 g1')
-- --       ( map-Σ Q4 g2 g2')
-- --       ( map-Σ Q4 f2 f2')
-- --       pr1 pr1 pr1 pr1
-- --       ( tot-square-over)
-- --       refl-htpy refl-htpy refl-htpy refl-htpy
-- --       ( bottom)
-- --   coh-tot-square-over (p , q) =
-- --     ap-pr1-eq-pair-Σ (bottom p) (top q) ∙ inv right-unit

-- --   module _
-- --     (s1 : (p : P1) → Q1 p) (s2 : (p : P2) → Q2 p)
-- --     (s3 : (p : P3) → Q3 p) (s4 : (p : P4) → Q4 p)
-- --     (G1 : (p : P1) → g1' p (s1 p) ＝ s3 (g1 p))
-- --     (F1 : (p : P1) → f1' p (s1 p) ＝ s2 (f1 p))
-- --     (F2 : (p : P3) → f2' p (s3 p) ＝ s4 (f2 p))
-- --     (G2 : (p : P2) → g2' p (s2 p) ＝ s4 (g2 p))
-- --     where
-- --     open import foundation.action-on-identifications-binary-functions

-- --     lemma :
-- --       pasting-vertical-coherence-square-maps g1
-- --         ( map-section-family s1) (map-section-family s3)
-- --         ( tot-map-over g1 g1') (tot-map-over f1 f1')
-- --         ( tot-map-over {B' = Q4} f2 f2') (tot-map-over g2 g2')
-- --         ( eq-pair-eq-fiber ∘ G1)
-- --         ( coherence-square-maps-Σ Q4 g1' f1' f2' g2' (λ p → top {p})) ~
-- --       ( λ p → eq-pair-Σ (bottom p) (top (s1 p) ∙ ap (f2' (g1 p)) (G1 p)))
-- --     lemma = λ p → ap
-- --               ( eq-pair-Σ (bottom p) (top (s1 p)) ∙_)
-- --               ( [i] p) ∙
-- --               ( inv (concat-vertical-eq-pair (bottom p) (top (s1 p)) (ap (f2' (g1 p)) (G1 p))))
-- --         where
-- --         [i] =
-- --           λ (p : P1) →
-- --           inv (ap-comp (map-Σ Q4 f2 f2') (pair (g1 p)) (G1 p)) ∙
-- --           ap-comp (pair (f2 (g1 p))) (f2' (g1 p)) (G1 p)

-- --     section-cube-over-sect-square-over :
-- --       section-square-over g1 f1 f2 g2
-- --         ( g1' _) (f1' _) (f2' _) (g2' _)
-- --         s1 s2 s3 s4
-- --         G1 F1 F2 G2
-- --         bottom top →
-- --       section-displayed-cube-over f1 g1 g2 f2
-- --         ( tot-map-over f1 f1')
-- --         ( tot-map-over g1 g1')
-- --         ( tot-map-over g2 g2')
-- --         ( tot-map-over f2 f2')
-- --         pr1 pr1 pr1 pr1
-- --         ( coherence-square-maps-Σ Q4 g1' f1' f2' g2' (λ p → top {p}))
-- --         refl-htpy refl-htpy refl-htpy refl-htpy
-- --         ( bottom)
-- --         ( coh-tot-square-over)
-- --     pr1 (section-cube-over-sect-square-over α) =
-- --       ( section-dependent-function s1) ,
-- --       ( section-dependent-function s2) ,
-- --       ( eq-pair-eq-fiber ∘ F1) ,
-- --       ( λ p → right-unit ∙ ap-pr1-eq-pair-Σ refl (F1 p))
-- --     pr1 (pr2 (section-cube-over-sect-square-over α)) =
-- --       ( section-dependent-function s3) ,
-- --       ( section-dependent-function s4) ,
-- --       ( eq-pair-eq-fiber ∘ F2) ,
-- --       ( λ p → right-unit ∙ ap-pr1-eq-pair-Σ refl (F2 p))
-- --     pr2 (pr2 (section-cube-over-sect-square-over α)) =
-- --       ( eq-pair-eq-fiber ∘ G1) ,
-- --       ( λ p → right-unit ∙ ap-pr1-eq-pair-Σ refl (G1 p)) ,
-- --       ( eq-pair-eq-fiber ∘ G2) ,
-- --       ( λ p → right-unit ∙ ap-pr1-eq-pair-Σ refl (G2 p)) ,
-- --       ( λ p →
-- --         ap-binary
-- --           ( _∙_)
-- --           ( pasting-horizontal-comp f1' g2' s1 s2 s4 F1 G2 p)
-- --           ( ap-map-section-family-lemma s4 (bottom p)) ∙
-- --         {!!} ∙
-- --         ap (eq-pair-Σ (bottom p)) (inv (α p) ∙ assoc (top (s1 p)) (ap (f2' (g1 p)) (G1 p)) (F2 (g1 p))) ∙
-- --         concat-vertical-eq-pair
-- --           ( bottom p)
-- --           ( top (s1 p))
-- --           ( ap (f2' (g1 p)) (G1 p) ∙ F2 (g1 p)) ∙
-- --         ap-binary
-- --           ( _∙_)
-- --           ( refl {x = eq-pair-Σ (bottom p) (top (s1 p))})
-- --           ( inv (pasting-horizontal-comp g1' f2' s1 s3 s4 G1 F2 p))) ,
-- --       {!!}
-- -- ```
