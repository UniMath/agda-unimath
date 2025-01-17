# Stuff over other stuff

```agda
module synthetic-homotopy-theory.stuff-over where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-identifications
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.transposition-identifications-along-equivalences
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-homotopies-concatenation
```

</details>

```agda
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
  htpy-over = {a : A} (a' : A' a) → dependent-identification B' (H a) (f' a') (g' a')

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
  inv-htpy-over H' a' =
    map-eq-transpose-equiv-inv (equiv-tr B' (H _)) (inv (H' a'))

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
  left-whisk-htpy-over {a} a' =
    ind-htpy f
      ( LWMOTIF a')
      ( ap s')
      ( H)
      ( H' a')

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : A → UU l4} {B' : B → UU l5} {X' : X → UU l6}
  {f : A → B}
  {f' g' : {a : A} → A' a → B' (f a)}
  (H' : {a : A} → f' {a} ~ g')
  {s : B → X} (s' : {b : B} → B' b → X' (s b))
  where

  compute-left-whisk-htpy-over :
    {a : A} (a' : A' a) →
    left-whisk-htpy-over {B' = B'} {X' = X'} {f = f} refl-htpy H' s' a' ＝ ap s' (H' a')
  compute-left-whisk-htpy-over a' =
    htpy-eq
      ( htpy-eq-implicit
        ( compute-ind-htpy f
          ( LWMOTIF {B' = B'} {X' = X'} refl-htpy H' s' a')
          ( ap s'))
        ( g' a'))
      ( H' a')

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
    (a : A) →
    H' (sA a) ∙ G a ＝
    ap (tr B' (H a)) (F a) ∙ apd sB (H a)

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
  inv-section-htpy-over α =
    ind-htpy f
      ( λ g H →
        {g' : {a : A} → A' a → B' (g a)} →
        (H' : htpy-over B' H f' g') →
        (G : section-map-over g g' sA sB) →
        section-htpy-over H H' sA sB F G →
        section-htpy-over
          ( inv-htpy H)
          ( inv-htpy-over B' H f' g' H')
          sA sB G F)
      ( λ H' G α a →
        ind-htpy f'
          ( λ g'a H'a →
            (Ga : g'a (sA a) ＝ sB (f a)) →
            (αa : H'a (sA a) ∙ Ga ＝ ap (tr B' refl) (F a) ∙ apd sB refl) →
            map-eq-transpose-equiv-inv (equiv-tr B' refl) (inv (H'a (sA a))) ∙ F a ＝
            ap (tr B' refl) Ga ∙ apd sB refl)
          ( λ Ga αa →
            ap (_∙ F a) (compute-refl-eq-transpose-equiv-inv (equiv-tr B' refl)) ∙
            inv (right-unit ∙ ap-id _ ∙ (αa ∙ right-unit ∙ ap-id _)))
          ( H')
          ( G a)
          ( α a))
      ( H)
      ( H')
      ( G)
      ( α)

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

  right-whisk-section-htpy-over :
    section-htpy-over (H ·r s)
      ( right-whisk-htpy-over H H' s s')
      sX sB
      ( comp-section-map-over f s f' s' sX sA sB F S)
      ( comp-section-map-over g s g' s' sX sA sB G S)
  right-whisk-section-htpy-over =
    ind-htpy f
      ( λ g H →
          {g' : {a : A} → A' a → B' (g a)}
          (H' : htpy-over B' H f' g')
          (G : section-map-over g g' sA sB)
          (α : section-htpy-over H H' sA sB F G) →
          section-htpy-over (H ·r s)
            ( right-whisk-htpy-over H H' s s')
            sX sB
            ( comp-section-map-over f s f' s' sX sA sB F S)
            ( comp-section-map-over g s g' s' sX sA sB G S))
      ( λ H' G α x →
        ind-htpy (f' {s x})
          ( λ g'sx H'sx →
            (Gsx : g'sx (sA (s x)) ＝ sB (f (s x)))
            (αsx : H'sx (sA (s x)) ∙ Gsx ＝ ap (tr B' refl) (F (s x)) ∙ apd sB refl) →
            H'sx (s' (sX x)) ∙ ((ap g'sx (S x)) ∙ Gsx) ＝
            ap (tr B' refl) (ap f' (S x) ∙ (F (s x))) ∙ apd sB refl)
          ( λ Gsx αsx → inv (right-unit ∙ (ap-id _ ∙ ap (ap f' (S x) ∙_) (inv (αsx ∙ (right-unit ∙ ap-id _))))))
          ( H')
          ( G (s x))
          ( α (s x)))
      ( H)
      ( H')
      ( G)
      ( α)

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
  left-whisk-section-htpy-over =
    ind-htpy f
      ( λ g H →
        {g' : {a : A} → A' a → B' (g a)} →
        (H' : htpy-over B' H f' g')
        (G : section-map-over g g' sA sB)
        (α : section-htpy-over H H' sA sB F G) →
        section-htpy-over (s ·l H)
          ( left-whisk-htpy-over H H' s')
          sA sX
          ( comp-section-map-over s f s' f' sA sB sX S F)
          ( comp-section-map-over s g s' g' sA sB sX S G))
      ( λ H' G α a →
        ap (_∙ (ap s' (G a) ∙ S (f a)))
          ( compute-left-whisk-htpy-over H' s' (sA a)) ∙
        ind-htpy f'
          ( λ g'a H'a →
            (Ga : g'a (sA a) ＝ sB (f a)) →
            (αa : H'a (sA a) ∙ Ga ＝ ap (tr B' refl) (F a) ∙ apd sB refl) →
            ap s' (H'a (sA a)) ∙ (ap s' Ga ∙ S (f a)) ＝ ap (tr X' refl) (ap s' (F a) ∙ S (f a)) ∙ apd sX refl)
          ( λ Ga αa → inv (right-unit ∙ (ap-id _ ∙ ap (_∙ S (f a)) (inv (ap (ap s') (αa ∙ (right-unit ∙ ap-id _)))))))
          ( H')
          ( G a)
          ( α a))
      ( H)
      ( H')
      ( G)
      ( α)

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
  concat-section-htpy-over =
    ind-htpy f
      ( λ g H →
        {i : A → B} (K : g ~ i)
        {g' : {a : A} → A' a → B' (g a)}
        {i' : {a : A} → A' a → B' (i a)}
        (H' : htpy-over B' H f' g') (K' : htpy-over B' K g' i')
        (G : section-map-over g g' sA sB)
        (I : section-map-over i i' sA sB)
        (α : section-htpy-over H H' sA sB F G)
        (β : section-htpy-over K K' sA sB G I) →
        section-htpy-over
          ( H ∙h K)
          ( concat-htpy-over H K H' K')
          sA sB F I)
      ( λ K H' K' G I α β a →
        ind-htpy (f' {a})
          ( λ g'a H' →
            {ia : B} (K : f a ＝ ia)
            {i'a : A' a → B' ia}
            (K' : (a' : A' a) → dependent-identification B' K (g'a a') (i'a a'))
            (G : g'a (sA a) ＝ sB (f a))
            (I : i'a (sA a) ＝ sB ia)
            (α : H' (sA a) ∙ G ＝ ap id (F a) ∙ refl)
            (β : K' (sA a) ∙ I ＝ ap (tr B' K) G ∙ apd sB K) →
              concat-dependent-identification B' refl K (H' (sA a)) (K' (sA a)) ∙ I ＝
              ap (tr B' K) (F a) ∙ apd sB K)
          ( λ K K' G I α β → β ∙ ap (λ p → ap (tr B' K) p ∙ apd sB K) (α ∙ (right-unit ∙ ap-id (F a))))
          ( H' {a})
          ( K a)
          ( K' {a})
          ( G a)
          ( I a)
          ( α a)
          ( β a))
      ( H)
      ( K)
      ( H')
      ( K')
      ( G)
      ( I)
      ( α)
      ( β)

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
        [i] = unget-section-triangle-over m g2 f2 m' g2' f2' s2 s3 s4 M G2 F2 B2 T2 S2
        [ii] = right-whisk-section-htpy-over B2 T2 s2 s4 _ _ [i] f1 f1' s1 F1
        [iii] = unget-section-triangle-over' f1 g1 m f1' g1' m' s1 s2 s3 F1 G1 M B1 T1 S1
        [iv] = left-whisk-section-htpy-over B1 T1 s1 s3 _ _ [iii] f2 f2' s4 F2
```
