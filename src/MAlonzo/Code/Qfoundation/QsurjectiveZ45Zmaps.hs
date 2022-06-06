{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QsurjectiveZ45Zmaps where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QpropositionalZ45Zmaps
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.Qfoundation.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QfibersZ45ZofZ45Zmaps
import qualified MAlonzo.Code.Qfoundation.QfunctorialityZ45ZdependentZ45ZfunctionZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations

-- foundation.surjective-maps.is-surjective
d_is'45'surjective_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> () -> (AgdaAny -> AgdaAny) -> ()
d_is'45'surjective_12 = erased
-- foundation.surjective-maps.is-surjective-has-section
d_is'45'surjective'45'has'45'section_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_is'45'surjective'45'has'45'section_30 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_is'45'surjective'45'has'45'section_30 v5 v6
du_is'45'surjective'45'has'45'section_30 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_is'45'surjective'45'has'45'section_30 v0 v1
  = case coe v0 of
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
        -> coe
             MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
             ()
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                (coe v2 v1) (coe v3 v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- foundation.surjective-maps.is-surjective-is-equiv
d_is'45'surjective'45'is'45'equiv_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
d_is'45'surjective'45'is'45'equiv_48 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_is'45'surjective'45'is'45'equiv_48 v5
du_is'45'surjective'45'is'45'equiv_48 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_is'45'surjective'45'is'45'equiv_48 v0
  = coe
      du_is'45'surjective'45'has'45'section_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
         (coe v0))
-- foundation.surjective-maps.dependent-universal-property-surj
d_dependent'45'universal'45'property'45'surj_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () -> () -> (AgdaAny -> AgdaAny) -> ()
d_dependent'45'universal'45'property'45'surj_64 = erased
-- foundation.surjective-maps.is-surjective-dependent-universal-property-surj
d_is'45'surjective'45'dependent'45'universal'45'property'45'surj_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny -> AgdaAny
d_is'45'surjective'45'dependent'45'universal'45'property'45'surj_92 ~v0
                                                                    ~v1 ~v2 ~v3 ~v4 v5
  = du_is'45'surjective'45'dependent'45'universal'45'property'45'surj_92
      v5
du_is'45'surjective'45'dependent'45'universal'45'property'45'surj_92 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny -> AgdaAny
du_is'45'surjective'45'dependent'45'universal'45'property'45'surj_92 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'inv'45'is'45'equiv_216
      (coe
         v0 ()
         (\ v1 ->
            coe
              MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.d_trunc'45'Prop_32
              () erased))
      (\ v1 ->
         coe
           MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
           ()
           (coe
              MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
              (coe v1) erased))
-- foundation.surjective-maps.square-dependent-universal-property-surj
d_square'45'dependent'45'universal'45'property'45'surj_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_square'45'dependent'45'universal'45'property'45'surj_134 = erased
-- foundation.surjective-maps.dependent-universal-property-surj-is-surjective
d_dependent'45'universal'45'property'45'surj'45'is'45'surjective_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_dependent'45'universal'45'property'45'surj'45'is'45'surjective_152 ~v0
                                                                     v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_dependent'45'universal'45'property'45'surj'45'is'45'surjective_152
      v1 v5 v6 v7
du_dependent'45'universal'45'property'45'surj'45'is'45'surjective_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_dependent'45'universal'45'property'45'surj'45'is'45'surjective_152 v0
                                                                      v1 v2 v3
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'comp''_370
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'equiv'45'comp''_370
         (coe
            MAlonzo.Code.Qfoundation.QfunctorialityZ45ZdependentZ45ZfunctionZ45Ztypes.du_is'45'equiv'45'map'45'Π_152
            (coe v0)
            (coe
               (\ v4 ->
                  coe
                    MAlonzo.Code.Qfoundation.QcontractibleZ45Ztypes.du_is'45'equiv'45'diagonal'45'is'45'contr_336
                    (coe
                       MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'proof'45'irrelevant'45'is'45'prop_112
                       (coe
                          MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_is'45'prop'45'type'45'trunc'45'Prop_18
                          (coe ()))
                       (coe v1 v4)))))
         (coe
            MAlonzo.Code.Qfoundation.QfunctorialityZ45ZdependentZ45ZfunctionZ45Ztypes.du_is'45'equiv'45'map'45'Π_152
            (coe v0)
            (coe
               (\ v4 ->
                  coe
                    MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_is'45'propositional'45'truncation'45'trunc'45'Prop_148
                    () v2 (coe v3 v4)))))
      (coe
         MAlonzo.Code.Qfoundation.QfibersZ45ZofZ45Zmaps.du_is'45'equiv'45'map'45'reduce'45'Π'45'fib_180)
-- foundation.surjective-maps.equiv-dependent-universal-property-surj-is-surjective
d_equiv'45'dependent'45'universal'45'property'45'surj'45'is'45'surjective_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'dependent'45'universal'45'property'45'surj'45'is'45'surjective_216 v0
                                                                              ~v1 v2 ~v3 ~v4 v5 v6
                                                                              v7
  = du_equiv'45'dependent'45'universal'45'property'45'surj'45'is'45'surjective_216
      v0 v2 v5 v6 v7
du_equiv'45'dependent'45'universal'45'property'45'surj'45'is'45'surjective_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'dependent'45'universal'45'property'45'surj'45'is'45'surjective_216 v0
                                                                               v1 v2 v3 v4
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe (\ v5 v6 -> coe v5 (coe v2 v6)))
      (coe
         du_dependent'45'universal'45'property'45'surj'45'is'45'surjective_152
         (coe v1) (coe v3) (coe v0) (coe v4))
-- foundation.surjective-maps.is-surjective-is-propositional-truncation
d_is'45'surjective'45'is'45'propositional'45'truncation_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny -> AgdaAny
d_is'45'surjective'45'is'45'propositional'45'truncation_246 ~v0 ~v1
                                                            ~v2 ~v3 ~v4 v5
  = du_is'45'surjective'45'is'45'propositional'45'truncation_246 v5
du_is'45'surjective'45'is'45'propositional'45'truncation_246 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_14 ->
   (AgdaAny ->
    MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny -> AgdaAny
du_is'45'surjective'45'is'45'propositional'45'truncation_246 v0
  = coe
      du_is'45'surjective'45'dependent'45'universal'45'property'45'surj_92
      (coe v0)
-- foundation.surjective-maps.is-propsitional-truncation-is-surjective
d_is'45'propsitional'45'truncation'45'is'45'surjective_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'propsitional'45'truncation'45'is'45'surjective_264 ~v0 v1
                                                           ~v2 ~v3 ~v4 v5 v6
  = du_is'45'propsitional'45'truncation'45'is'45'surjective_264
      v1 v5 v6
du_is'45'propsitional'45'truncation'45'is'45'surjective_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'propsitional'45'truncation'45'is'45'surjective_264 v0 v1
                                                            v2
  = coe
      du_dependent'45'universal'45'property'45'surj'45'is'45'surjective_152
      (coe v0) (coe v1) (coe v2)
-- foundation.surjective-maps.is-equiv-is-emb-is-surjective
d_is'45'equiv'45'is'45'emb'45'is'45'surjective_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'is'45'emb'45'is'45'surjective_280 ~v0 ~v1 ~v2 ~v3
                                                   ~v4 v5 ~v6
  = du_is'45'equiv'45'is'45'emb'45'is'45'surjective_280 v5
du_is'45'equiv'45'is'45'emb'45'is'45'surjective_280 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'is'45'emb'45'is'45'surjective_280 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Zmaps.du_is'45'equiv'45'is'45'contr'45'map_60
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'proof'45'irrelevant'45'is'45'prop_112
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.QpropositionalZ45Zmaps.du_is'45'prop'45'map'45'is'45'emb_46)
              (coe
                 MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
                 (coe ()) (coe ()) (coe v0 v1)
                 (coe
                    MAlonzo.Code.QfoundationZ45Zcore.QpropositionalZ45Zmaps.du_fib'45'emb'45'Prop_84)
                 (coe (\ v2 -> v2)))))
-- foundation.surjective-maps._.is-surjective-comp
d_is'45'surjective'45'comp_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_is'45'surjective'45'comp_314 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               v9 v10 v11 v12
  = du_is'45'surjective'45'comp_314 v9 v10 v11 v12
du_is'45'surjective'45'comp_314 ::
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_is'45'surjective'45'comp_314 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
      (coe ()) (coe ()) (coe v1 v3)
      (coe
         MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.d_trunc'45'Prop_32
         () erased)
      (coe
         (\ v4 ->
            case coe v4 of
              MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v5 v6
                -> coe
                     MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
                     (coe ()) (coe ()) (coe v2 v5)
                     (coe
                        MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.d_trunc'45'Prop_32
                        () erased)
                     (coe
                        (\ v7 ->
                           case coe v7 of
                             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v8 v9
                               -> coe
                                    MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
                                    ()
                                    (coe
                                       MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                                       (coe v8) (coe v0 v8))
                             _ -> MAlonzo.RTE.mazUnreachableError))
              _ -> MAlonzo.RTE.mazUnreachableError))
-- foundation.surjective-maps._.is-surjective-comp'
d_is'45'surjective'45'comp''_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_is'45'surjective'45'comp''_350 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_is'45'surjective'45'comp''_350
du_is'45'surjective'45'comp''_350 ::
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_is'45'surjective'45'comp''_350
  = coe du_is'45'surjective'45'comp_314 erased
-- foundation.surjective-maps._.is-surjective-left-factor
d_is'45'surjective'45'left'45'factor_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_is'45'surjective'45'left'45'factor_378 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                         ~v6 ~v7 v8 ~v9 v10 v11
  = du_is'45'surjective'45'left'45'factor_378 v8 v10 v11
du_is'45'surjective'45'left'45'factor_378 ::
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_is'45'surjective'45'left'45'factor_378 v0 v1 v2
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
      (coe ()) (coe ()) (coe v1 v2)
      (coe
         MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.d_trunc'45'Prop_32
         () erased)
      (coe
         (\ v3 ->
            case coe v3 of
              MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v4 v5
                -> coe
                     MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_unit'45'trunc'45'Prop_12
                     ()
                     (coe
                        MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                        (coe v0 v4) erased)
              _ -> MAlonzo.RTE.mazUnreachableError))
-- foundation.surjective-maps._.is-surjective-left-factor'
d_is'45'surjective'45'left'45'factor''_408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_is'45'surjective'45'left'45'factor''_408 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                           ~v6 v7
  = du_is'45'surjective'45'left'45'factor''_408 v7
du_is'45'surjective'45'left'45'factor''_408 ::
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_is'45'surjective'45'left'45'factor''_408 v0
  = coe du_is'45'surjective'45'left'45'factor_378 (coe v0)
