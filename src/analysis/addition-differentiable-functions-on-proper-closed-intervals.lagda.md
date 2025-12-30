```agda
module _
  {l1 l2 l3 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : type-proper-closed-interval-ℝ l1 [a,b] → ℝ l2)
  (g : type-proper-closed-interval-ℝ l1 [a,b] → ℝ l3)
  (f' : type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l2))
  (g' : type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l3))
  (is-derivative-f-f' :
    is-derivative-real-function-proper-closed-interval-ℝ [a,b] f f')
  (is-derivative-g-g' :
    is-derivative-real-function-proper-closed-interval-ℝ [a,b] g g')
  where

  abstract
    is-derivative-add-real-function-proper-closed-interval-ℝ :
      is-derivative-real-function-proper-closed-interval-ℝ
        ( [a,b])
        ( λ x → f x +ℝ g x)
        ( λ x → f' x +ℝ g' x)
    is-derivative-add-real-function-proper-closed-interval-ℝ =
      let
        open
          do-syntax-trunc-Prop
            ( is-derivative-prop-real-function-proper-closed-interval-ℝ
              ( [a,b])
              ( λ x → f x +ℝ g x)
              ( λ x → f' x +ℝ g' x))
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in do
        (μ , is-mod-μ) ← is-derivative-f-f'
        (ν , is-mod-ν) ← is-derivative-g-g'
        is-derivative-modulus-of-real-function-proper-closed-interval-ℝ [a,b]
          ( _)
          ( _)
          ( λ ε →
            let
              (ε₁ , ε₂ , ε₁+ε₂=ε) = split-ℚ⁺ ε
            in
              ( min-ℚ⁺ (μ ε₁) (ν ε₂) ,
                λ x y Nxy →
                chain-of-inequalities
                  dist-ℝ
                    ( (f y +ℝ g y) -ℝ (f x +ℝ g x))
                    ( (f' x +ℝ g' x) *ℝ (pr1 y -ℝ pr1 x))
                  ≤ dist-ℝ
                      ( (f y -ℝ f x) +ℝ (g y -ℝ g x))
                      ( f' x *ℝ (pr1 y -ℝ pr1 x) +ℝ g' x *ℝ (pr1 y -ℝ pr1 x))
                    by
                      leq-eq-ℝ
                        ( ap-dist-ℝ
                          ( interchange-law-diff-add-ℝ _ _ _ _)
                          ( right-distributive-mul-add-ℝ _ _ _))
                  ≤ abs-ℝ
                      ( ( (f y -ℝ f x) -ℝ f' x *ℝ (pr1 y -ℝ pr1 x)) +ℝ
                        ( (g y -ℝ g x) -ℝ g' x *ℝ (pr1 y -ℝ pr1 x)))
                    by
                      leq-eq-ℝ (ap abs-ℝ (interchange-law-diff-add-ℝ _ _ _ _))
                  ≤ ( dist-ℝ (f y -ℝ f x) (f' x *ℝ (pr1 y -ℝ pr1 x))) +ℝ
                    ( dist-ℝ (g y -ℝ g x) (g' x *ℝ (pr1 y -ℝ pr1 x)))
                    by triangle-inequality-abs-ℝ _ _
                  ≤ ( real-ℚ⁺ ε₁ *ℝ dist-ℝ (pr1 x) (pr1 y)) +ℝ
                    ( real-ℚ⁺ ε₂ *ℝ dist-ℝ (pr1 x) (pr1 y))
                    by
                      preserves-leq-add-ℝ
                        ( is-mod-μ
                          ( ε₁)
                          ( x)
                          ( y)
                          ( weakly-monotonic-neighborhood-Metric-Space
                            ( metric-space-ℝ l1)
                            ( pr1 x)
                            ( pr1 y)
                            ( min-ℚ⁺ (μ ε₁) (ν ε₂))
                            ( μ ε₁)
                            ( leq-left-min-ℚ⁺ _ _)
                            ( Nxy)))
                        ( is-mod-ν
                          ( ε₂)
                          ( x)
                          ( y)
                          ( weakly-monotonic-neighborhood-Metric-Space
                            ( metric-space-ℝ l1)
                            ( pr1 x)
                            ( pr1 y)
                            ( min-ℚ⁺ (μ ε₁) (ν ε₂))
                            ( ν ε₂)
                            ( leq-right-min-ℚ⁺ _ _)
                            ( Nxy)))
                  ≤ (real-ℚ⁺ ε₁ +ℝ real-ℚ⁺ ε₂) *ℝ dist-ℝ (pr1 x) (pr1 y)
                    by leq-eq-ℝ (inv (right-distributive-mul-add-ℝ _ _ _))
                  ≤ real-ℚ⁺ (ε₁ +ℚ⁺ ε₂) *ℝ dist-ℝ (pr1 x) (pr1 y)
                    by leq-eq-ℝ (ap-mul-ℝ (add-real-ℚ _ _) refl)
                  ≤ real-ℚ⁺ ε *ℝ dist-ℝ (pr1 x) (pr1 y)
                    by leq-eq-ℝ (ap-mul-ℝ (ap real-ℚ⁺ ε₁+ε₂=ε) refl)))
```
